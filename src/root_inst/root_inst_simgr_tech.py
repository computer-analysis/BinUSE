from angr import ExplorationTechnique
import signal
from contextlib import contextmanager
from angr.sim_options import *
from src.root_inst.root_inst_plugin import *
from src.simple_cfg import *
from src.utils import *
from collections import defaultdict
from src.error import TimeoutForCollectingInfoException
import claripy

finish_stash = 'finish'


class RootInstTech(ExplorationTechnique):

    def __init__(self, base_entry, p: angr.Project, move_to=finish_stash, verbose=0):
        super(RootInstTech, self).__init__()
        self.base_entry = base_entry
        self.p = p
        self.move_to = move_to
        self.verbose = verbose
        self.exe_ranges = get_executable_ranges(self.p)
        self.data_ranges = get_data_ranges(self.p)
        self.visited_ribs = dict()
        self.visited_rib_starts = {base_entry}
        self.simple_cfg = SimpleCFG()

    def create_state(self, addr, parent_id):
        state = self.p.factory.blank_state(addr=addr, plugins={'ri': RootInstPlugin(parent_id=parent_id)})
        return state

    def add_node_to_simple_cfg(self, state):
        rib_id = state.ri.get_rib_id()
        self.simple_cfg.add_node(SimpleCFGNode(rib_id, is_call=False))
        self.simple_cfg.add_child_to(state.ri.parent_id, rib_id)

    def step_state(self, simgr, state, **kwargs):
        if state.ri.for_all_step():
            try:
                if state.ri.ends_rib():
                    state.ri.for_end_rib_step()
                    rib_id = state.ri.get_rib_id()

                    self.add_node_to_simple_cfg(state)

                    sucs = state.step(**kwargs)
                    formulas, constraints, read_from = FormulaExtractor.get_se_info(sucs, state.ri.writing_records,
                                                                                    set())
                    self.visited_ribs[rib_id] = FormulaExtractor.transform_to_ted_format(
                        formulas, constraints, read_from, self.exe_ranges, self.data_ranges)
                    # formulas info has been collected, then get the state into the following block
                    stashes = {'active': [], finish_stash: sucs.unconstrained_successors}
                    for s in sucs.flat_successors:
                        if s.callstack.ret_addr in self.visited_rib_starts:
                            continue
                        new_state = self.create_state(s.callstack.ret_addr, parent_id=rib_id)
                        # we should never visit this block later
                        self.visited_rib_starts.add(new_state.addr)
                        stashes['active'].append(new_state)
                    return stashes
                else:
                    return simgr.step_state(state, **kwargs)
            except Exception as e:
                return {'active': [], finish_stash: []}
        else:
            # the state has no valid block, move it to finish_stash
            return {'active': [], finish_stash: []}


@contextmanager
def _time_limit_for_a_step(seconds, basic_block_id):
    def signal_handler(signum, frame):
        raise TimeoutForCollectingInfoException(basic_block_id)

    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)


class ContinuousInfoTech(ExplorationTechnique):

    def __init__(self, base_entry, p: angr.Project, fe: FormulaExtractor,
                 ida_scfg: SimpleCFG, callees, move_to=finish_stash, max_depth=1000):
        super(ContinuousInfoTech, self).__init__()
        self.base_entry = base_entry
        self.p = p
        self.fe = fe
        self.scfg = ida_scfg
        self.callees = callees
        self.move_to = move_to
        self.max_depth = max_depth

        # store all lips, every lip is a tuple of RIBs
        self.ri_lips = []
        self.init_state = None

        # the key is RIB, and the relative denotes a list of LIPs whose last RIB is the key
        self.rib_relative = defaultdict(list)

    def create_init_state(self):
        assert self.init_state is None
        self.init_state = self.p.factory.blank_state(addr=self.base_entry,
                                                     plugins={'ci': ContinuousInfoPlugin()},
                                                     # add_options=simplification | symbolic | {ABSTRACT_MEMORY}
                                                     )
        return self.init_state

    def mv_state_ip(self, state, v):
        self.fe._set_state_ip_func(state, v)

    def merge_fe_formulas(self, fc_list: list):
        return merge_fe_formulas(fc_list, self.fe.ptr_size)

    def merge_rib_formulas_and_constraints(self):
        for rib, relatives in self.rib_relative.items():
            self.fe._visited_ci[rib] = [self.fe._visited[lip] for lip in relatives]
        # if len(relatives) == 1:
        #     self.fe._visited_ci[rib] = self.fe._visited[rib]
        # else:
        #     # this means there are multiple paths which can reach this RIB
        #     # we use If node to merge multiple formulas together
        #     # the structure of a If node:
        #     # args[0]: if constraint
        #     # args[1]: ast when if constraint is satisfied
        #     # args[2]: ast of else
        #
        #     # the merge process merely
        #
        #     # the content is a pair (And(*constraints), formulas)
        #     pass

    def step_state(self, simgr, state, **kwargs):
        do_se, has_succ, ends_ri, ends_se = state.ci.for_all_step(self.scfg, self.callees)
        if not do_se:
            # meet loop in most cases
            # we simply discard all back edges currently
            return {None: [], self.move_to: []}

        lip = tuple(state.ci.path_history)
        if len(lip) > self.max_depth:
            # too long path, give up it
            return {None: [], self.move_to: []}

        if not ends_ri:
            # for something like switch, there are tremendous number of successors
            # we simply give up on this condition
            tmp = simgr.step_state(state, **kwargs)
            if len(tmp[None]) > 10:
                return {None: [], self.move_to: []}
            return tmp

        try:
            with _time_limit_for_a_step(60, basic_block_id=state.addr):
                # the cache process may timeout, it seems something wrong with claripy
                # a huge depth of shallow_repr
                sucs = state.step(**kwargs)
                # cache the formulas inside formula extractor directly
                self.fe._cache_formuals_from_sucs(sucs, lip, self.init_state, self.callees)
                ri_lip = tuple(state.ci.ri_path_history)
                self.fe._visited[ri_lip] = self.fe._visited[lip]
                self.fe._visited_smt[ri_lip] = self.fe._visited_smt[lip]

            last_rib = ri_lip[-1]
            self.rib_relative.setdefault(last_rib, []).append(ri_lip)

            # we merely check the first 2 calls on each LIP
            if len(ri_lip) > 1:
                self.ri_lips.append(ri_lip)
                return {None: [], self.move_to: []}

            if has_succ and not ends_se:
                if len(sucs.flat_successors) == 1 and len(self.scfg.pool[state.addr].children) == 1:
                    succ_state = sucs.flat_successors[0]
                    succ_ip = next(iter(self.scfg.pool[state.addr].children))
                    self.mv_state_ip(succ_state, succ_ip)
                    self.fe._reset_state_return_reg_func(succ_state)
                    return {None: [succ_state], self.move_to: []}
                else:
                    # do not know how to do it, if there is at least 1 active successor, do the same
                    if len(sucs.all_successors) >= 1 and len(self.scfg.pool[state.addr].children) >= 1:
                        succ_state = sucs.all_successors[0]
                        succ_ip = next(iter(self.scfg.pool[state.addr].children))
                        self.mv_state_ip(succ_state, succ_ip)
                        self.fe._reset_state_return_reg_func(succ_state)
                        return {None: [succ_state], self.move_to: []}
                    else:
                        return {None: [], self.move_to: []}

            else:
                self.ri_lips.append(ri_lip)
                return {None: [], self.move_to: [sucs]}

        except TimeoutForCollectingInfoException as e:
            log.error("Too long time for collecting formulas: " + str(e))
            return {None: [], self.move_to: []}
        except angr.AngrError as e:
            log.error("meet error while collecting formulas and constraints from " +
                      str(state.ci.path_history + state.ci.rib) + ' Error Msg: ' + str(e))
            return {None: [], self.move_to: []}

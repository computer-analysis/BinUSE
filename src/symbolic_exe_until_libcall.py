from angr import ExplorationTechnique
from src.utils import *
from angr.state_plugins.plugin import SimStatePlugin
from src.formulas_extractor import FormulaExtractor, _time_limit_for_a_block
from angr.sim_options import resilience, UNDER_CONSTRAINED_SYMEXEC
from src.lib_call_arguments import *
from src.error import TimeoutForCollectingInfoException
from src.config_for_sym_exe import get_init_sp, init_state_sp
import claripy
import copy
import src

finish_stash = 'finish'


class SELimiterPlugin(SimStatePlugin):

    def __init__(self, loop_max=2, recur_max=2, trace_max=1000):
        super(SELimiterPlugin, self).__init__()
        self.loop_max = loop_max
        self.recur_max = recur_max
        self.trace_max = trace_max
        self.path_history = []
        self.call_stack = [0]
        self.traces_in_funcs = [[]]

    def set_state(self, state):
        super(SELimiterPlugin, self).set_state(state)

    def copy(self, _memo):
        n = SELimiterPlugin(self.loop_max, self.recur_max)
        n.path_history = self.path_history.copy()
        n.call_stack = self.call_stack.copy()
        n.traces_in_funcs = self.traces_in_funcs.copy()
        # n.path_history = copy.deepcopy(self.path_history)
        # n.call_stack = copy.deepcopy(self.call_stack)
        # n.traces_in_funcs = copy.deepcopy(self.traces_in_funcs)
        return n

    def merge(self, _others, _merge_conditions, _common_ancestor=None):
        return False

    def widen(self, _others):
        log.warning("Widening not implemented widen for %s" % self.__class__.__name__)

    def init_state(self):
        """
        Use this function to perform any initialization on the state at plugin-add time
        """
        pass

    def out_text_sec(self, text_range):
        return self.state.addr not in text_range

    def _occurrence_in_call_stack(self, func_addr):
        occ = 0
        for f in self.state.callstack:
            if f.current_function_address == func_addr:
                occ += 1
        return occ

    def call_stack_changed(self):
        if self.state.callstack.current_function_address == self.call_stack[-1] \
                and len(self.state.callstack) == len(self.call_stack):
            return False
        return True

    @staticmethod
    def tail_loop_occurrence(unit, trace, bound):
        unit_len = len(unit)
        trace_len = len(trace)
        for i in range(bound):
            e_idx = trace_len - i * unit_len
            b_idx = e_idx - unit_len
            if b_idx < 0 or trace[b_idx:e_idx] != unit:
                return False
        return True


    def in_loop(self):
        cur = self.state.addr
        # we do not treat it strictly, only see if cur occurred repeatedly
        same_idxs = []
        for idx in range(len(self.path_history)):
            if self.path_history[idx] == cur:
                same_idxs.append(idx)
        count = len(same_idxs)

        if count > 2:
            for loop_split in range(1, count // 3):
                loop_unit = self.path_history[same_idxs[0 - loop_split]:]
                if self.tail_loop_occurrence(loop_unit, self.path_history[:-len(loop_unit)], self.loop_max):
                    return True
        return False


    def for_all_step(self, all_func_entries: dict):
        do_se = True
        self.path_history.append(self.state.addr)
        if len(self.path_history) > self.trace_max:
            return False
        # recursive function limiter
        if self.call_stack_changed():
            tmp = len(self.state.callstack) - len(self.call_stack)
            if tmp == 1:
                # enter a callee
                if self.state.addr in all_func_entries:
                    self.call_stack.append(self.state.addr)
                    self.traces_in_funcs.append([])
                else:
                    raise Exception('fail to recognize a call')
            elif tmp == -1:
                # a return
                self.call_stack.pop()
                self.traces_in_funcs.pop()
            else:
                raise Exception('weird change of call stack')
        self.traces_in_funcs[-1].append(self.state.addr)

        # recurive call limiter
        occ = self._occurrence_in_call_stack(self.state.addr)
        if occ > self.recur_max:
            log.debug("%s reaches max recursion limit" % str(self.state))
            do_se = False

        if not do_se:
            return do_se
        # loop limiter
        if self.in_loop():
            log.debug("%s reaches max loop limit" % str(self.state))
            do_se = False
        # naive buggy loop limiter
        # occ = 0
        # for block_id in self.traces_in_funcs[-1]:
        #     if self.state.addr == block_id:
        #         occ += 1
        # if occ > self.loop_max:
        #     log.debug("%s reaches max loop limit" % str(self.state))
        #     do_se = False
        return do_se


class MemAddrPlugin(SimStatePlugin):
    """
    To use this plugin, we need to add some code in angr/state_plugins/symbolic_memory.py
    Around line 390
    if a is not None:
        # added by BinUSE
        if hasattr(self.state, 'memaddr'):
            self.state.memaddr.get_relative_symbol(e)
        # end BinUSE
        return a
    """

    def merge(self, _others, _merge_conditions, _common_ancestor=None):
        return False

    def widen(self, _others):
        log.warning("Widening not implemented widen for %s" % self.__class__.__name__)

    def __init__(self):
        super(MemAddrPlugin, self).__init__()
        self.mem_ptr_symbols = set()
        self.mem_ptr_symbols_str = set()
        self.offset_symbols = set()

    def has(self, bvs):
        return bvs in self.mem_ptr_symbols

    def get_relative_symbol(self, expr):
        """
        :param expr: The expr should be concretized to a memory address. We get all symbols being used.
        The symbols may be in 2 types:
        1. a memory address pointer
        2. a offset relative value
        Currently I hope the offset should be relatively small. Usually the offset is a constant.
        We only analyze the simplest a +/- b expression, since it is easy to decide which one is the pointer,
        and this should cover almost all cases
        :return:
        """
        if hasattr(expr, 'depth'):
            if expr.depth == 1 and expr.symbolic:
                # expr itself is a symbolic value, and it is used as a mem ptr
                self.mem_ptr_symbols.add(expr)
            elif expr.depth == 2 and expr.symbolic:
                if expr.op in {'__add__', '__sub__'}:
                    if len(expr.args) != 2:
                        log.warning('Unknown why add and sub operation with a single argument, %s (%s, %s), treat it as a single parameter without the operation.' % (str(expr), str(expr.op), str(expr.args)))
                        self.get_relative_symbol(expr.args[0])
                    else:
                        if expr.args[0].symbolic and not expr.args[1].symbolic:
                            # args[1] should be a BVV, and its value should be relatively small (a offset)
                            self.mem_ptr_symbols.add(expr.args[0])
                            self.mem_ptr_symbols_str.add(str(expr.args[0]))
                        elif not expr.args[0].symbolic and expr.args[1].symbolic:
                            self.mem_ptr_symbols.add(expr.args[1])
                            self.mem_ptr_symbols_str.add(str(expr.args[1]))
                        else:
                            log.warning('Unsolvable expression for concretizing memory address %s' % str(expr))
                            # raise NotImplementedError()
                else:
                    log.warning('Unsolvable expression for concretizing memory address %s' % str(expr))
                    # raise NotImplementedError()
            else:
                # It could be a very complex formula. 'If' condition is often in it, so we treat the whole formula as
                # an input, since it is usually not being simplified.
                tmp = claripy.simplify(expr)
                # we must simplify it. It seems the simplify of claripy merely sort the AST in an order
                self.mem_ptr_symbols.add(tmp)
                self.mem_ptr_symbols_str.add(str(tmp))

    def copy(self, _memo):
        m = MemAddrPlugin()
        m.mem_ptr_symbols = self.mem_ptr_symbols.copy()
        m.offset_symbols = self.offset_symbols.copy()
        return m


class StopAtLibCallTech(ExplorationTechnique):

    def __init__(self, base_entry, p: angr.Project, fe: FormulaExtractor,
                 libcalls: dict, all_func_entries: dict, move_to=finish_stash):
        super(StopAtLibCallTech, self).__init__()
        self.base_entry = base_entry
        self.p = p
        self.fe = fe
        self.libcalls = libcalls  # items are (entry, name)
        self.all_func_entries = all_func_entries
        self.move_to = move_to
        self.exe_ranges = get_executable_ranges(self.p)
        self.text_range = get_section_range(self.p, '.text')
        self.data_ranges = get_data_ranges(self.p)
        self.init_state = None

        self.all_keys = []
        self.all_lib_calls = dict()

        self.call_args_map = None
        self.default_arg_read = None
        self.call_args_esp_offset = None
        self.default_args_esp_offset = None
        self.stack_args_enable = False
        if self.p.arch.name == 'AMD64':
            self.call_args_map = src.lib_call_arguments.X64_CALL_ARGUMENTS_MAP
            self.default_arg_read = {'rdi', 'rsi'}
        elif self.p.arch.name == 'X86':
            self.call_args_map = src.lib_call_arguments.X86_CALL_ARGUMENTS_MAP
            self.default_arg_read = {'edx', 'ecx'}
            self.default_args_esp_offset = [4, 8]
            self.stack_args_enable = True
        elif self.p.arch.name == 'AARCH64':
            self.call_args_map = src.lib_call_arguments.AARCH64_CALL_ARGUMENTS_MAP
            self.default_arg_read = {'x0', 'x1'}
        else:
            raise NotImplementedError()

    def create_init_state(self):
        assert self.init_state is None
        self.init_state = self.p.factory.blank_state(addr=self.base_entry,
                                                     plugins={'selimiter': SELimiterPlugin(),
                                                              'memaddr': MemAddrPlugin()},
                                                     add_options=resilience | {UNDER_CONSTRAINED_SYMEXEC}
                                                     # add_options=simplification | symbolic | {ABSTRACT_MEMORY}
                                                     )
        # if self.p.arch.name == 'AMD64':
        #     self.init_state.regs.rsp = claripy.BVV(0x7ffffffffff00000, 64)
        # elif self.p.arch.name == 'X86':
        #     self.init_state.regs.esp = claripy.BVV(0x7ffff000, 32)
        # elif self.p.arch.name == 'AARCH64':
        #     self.init_state.regs.sp = claripy.BVV(0x7ffffffffff00000, 64)
        init_state_sp(self.init_state)
        return self.init_state

    def get_libcall_reg_read(self, libcall_name):
        if self.p.arch.name == 'X86':
            return set()
        if libcall_name in self.call_args_map:
            reg_read = self.call_args_map[libcall_name]
        else:
            reg_read = self.default_arg_read
        return reg_read

    def get_libcall_mem_read(self, libcall_name, stack_ptr_v):
        if libcall_name in self.call_args_map and self.call_args_map[libcall_name] is None:
            return None
        if libcall_name in self.call_args_map:
            mem_read = [stack_ptr_v + offset for offset in self.call_args_map[libcall_name]]
        else:
            mem_read = [stack_ptr_v + offset for offset in self.default_args_esp_offset]
        return mem_read

    def step_state(self, simgr, state, **kwargs):
        log.debug('The number of states are %d' % len(simgr.stashes['active']))
        log.debug('Current trace of state: %s' % str(state.selimiter.path_history))
        log.debug('Current state: %s' % str(state))
        if len(self.all_keys) + len(simgr.unconstrained) >= 120:
            log.warning('Reach max libcall records. DIscard all active states')
            return {None: [], self.move_to: []}
        if len(simgr.stashes['active']) >= 2000:
            # angr may meet large swith structure and the number of states rises exponentially
            # discard all info
            # self.all_keys.clear()
            # keep current info
            # do nothing
            log.warning('Reach max states limit. Discard all active states')
            return {None: [], self.move_to: []}
        if state.selimiter.out_text_sec(self.text_range):
            state.selimiter.path_history.append(state.addr)
            # it is likely in a lib call
            if state.addr in self.libcalls.keys():
                # here is a trick, the last block_id is supposed to be the entry of a lib call
                # therefore, we use the lib call to check whether we should compare 2 trace
                self.all_keys.append(tuple(state.selimiter.path_history))
                # some lib calls need to identify meaningful arguments at special locations
                libcall_name = self.libcalls[state.addr]
                log.debug('The lib call name is %s (%s)' % (libcall_name, self.p.filename))
                reg_read = self.get_libcall_reg_read(libcall_name)
                if self.stack_args_enable:
                    mem_read = self.get_libcall_mem_read(libcall_name, state.solver.eval(state.regs.esp))
                else:
                    mem_read = set()
                self.fe.cache_formulas_from_state(state, tuple(state.selimiter.path_history), self.init_state, None,
                                                  reg_read=reg_read, mem_read=mem_read)

                # record the lib call, and add a relative path to this lib call
                if state.addr not in self.all_lib_calls:
                    self.all_lib_calls[state.addr] = []
                self.all_lib_calls[state.addr].append(tuple(state.selimiter.path_history))

                # for some special libcalls, we allow continuous symbolic execution to next libcall
                # continuous_libcalls = {'.__errno_location'}
                continuous_libcalls = set()
                if self.libcalls[state.addr] in continuous_libcalls:
                    # 2 step and we should return to the instruction after call .__errno_location
                    log.debug(f'go through {self.libcalls[state.addr]}')
                    tmp_sucs = state.step()
                    if tmp_sucs.flat_successors:
                        tmp_sucs = tmp_sucs.flat_successors[0].step()
                        return {None: tmp_sucs.flat_successors, self.move_to: []}
                    else:
                        return {None: [], self.move_to: []}
                else:
                    return {None: [], self.move_to: []}
            else:
                log.warning('IP register is not in text section and not in lib functions! init_state(0x%x), '
                            'execution trace %s' % (self.init_state.addr, str(state.selimiter.path_history)))
                # return simgr.step_state(state)
                # collect formulas here anyway
                self.all_keys.append(tuple(state.selimiter.path_history))
                if self.stack_args_enable:
                    mem_read = self.get_libcall_mem_read(None, state.solver.eval(state.regs.esp))
                else:
                    mem_read = set()
                self.fe.cache_formulas_from_state(state, tuple(state.selimiter.path_history), self.init_state, None,
                                                  reg_read=self.default_arg_read, mem_read=mem_read)
                if state.addr not in self.all_lib_calls:
                    self.all_lib_calls[state.addr] = []
                self.all_lib_calls[state.addr].append(tuple(state.selimiter.path_history))
                return {None: [], self.move_to: []}
        elif state.selimiter.for_all_step(all_func_entries=self.all_func_entries):
            try:
                # set a time limit for symbolic execution on every block
                # I met problems when running on -m32 -O0 expr, function bkm_scale_by_power(0x68ff)
                with _time_limit_for_a_block(30, state.addr):
                    tmp = simgr.step_state(state)
                    return tmp
            except TimeoutForCollectingInfoException as e:
                log.debug('Timeout a step for %s (%s)' % (str(state), self.p.filename))
                return {None: [], self.move_to: []}
        else:
            log.debug('Discard a state %s (%s)' % (str(state), self.p.filename))
            return {None: [], self.move_to: []}

    def get_info_from_return_paths(self, simgr):
        for s in simgr.unconstrained:
            rib = tuple(s.selimiter.path_history + [None])
            self.all_keys.append(rib)
            self.fe.cache_constraint_from_state(s, rib, self.init_state)

    def merge_path_to_same_lib_call_together(self):
        res = dict()
        for libcall_addr in self.all_lib_calls.keys():
            try:
                res[libcall_addr] = []
                all_paths = self.all_lib_calls[libcall_addr]
                all_formulas = dict()
                all_cons = []
                for path in all_paths:
                    fs, cs, inputs = self.fe.get_formulas_from(path)
                    if cs:
                        all_cons.extend(cs)
                    for f in fs:
                        v_name, ast = f
                        if v_name not in all_formulas:
                            all_formulas[v_name] = []
                        all_formulas[v_name].append((ast, cs))
                if len(all_formulas.keys()) > 0:
                    # here is a libcall with arguments
                    for v_name, fc_list in all_formulas.items():
                        tmp_f, tmp_cons = merge_fe_formulas(fc_list, self.fe.ptr_size)
                        tmp_f = claripy.simplify(tmp_f)
                        if len(tmp_cons) == 0:
                            # no constraints is equivalent to always True
                            tmp_cons = None
                        else:
                            tmp_cons = claripy.simplify(claripy.Or(*tmp_cons))
                            if tmp_cons.depth == 1 and tmp_cons.args == (True,):
                                tmp_cons = None
                        res[libcall_addr].append((v_name, tmp_f, tmp_cons))
                else:
                    # here is a libcall with no argument
                    if len(all_cons) == 0:
                        tmp_cons = claripy.BoolV(True)
                    else:
                        tmp_cons = claripy.simplify(claripy.Or(*all_cons))
                    res[libcall_addr].append((None, all_paths, tmp_cons))
            except Exception:
                log.error('meets error in merge_path_to_same_lib_call_together base_entry=0x%x' % self.base_entry)
                # if this lib call meets error, we skip merging formulas of it
                if libcall_addr in res.keys():
                    res.pop(libcall_addr)
        return res

# from src.detector import Detector
# if __name__ == '__main__':
#     p = load_proj('samples/coreutils_O0/true')
#     p1 = load_proj('samples/coreutils_O3/true')
#     d = Detector(p, p1, mode='smt', alg='cop')
#     all_func_map = d._get_func_addr_name_map(0)
#     libcalls = dict()
#     for f_addr, f_name in all_func_map.items():
#         if f_name.startswith('.'):
#             libcalls[f_addr] = f_name
#     # cfg = p.analyses.CFGFast()
#     main_addr = 4200971
#     tech = StopAtLibCallTech(main_addr, p, d._fe[0], libcalls, all_func_map)
#     init_state = tech.create_init_state()
#     sim_manager = p.factory.simgr(init_state, techniques=[tech])
#     sim_manager.run()
#
#     for k, info in d._fe[0]._visited.items():
#         print('%s : %s' % (str(k), str(info)))
#

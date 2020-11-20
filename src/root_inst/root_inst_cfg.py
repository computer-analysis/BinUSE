import os
import signal
from contextlib import contextmanager

from src.root_inst.root_inst_simgr_tech import *
from src.error import TimeoutForCollectingInfoException


def _path_contain_root_inst(path, cfg):
    for block_id in path:
        if ends_with_root_instr(cfg.model.get_any_node(block_id).block):
            return True
    return False


def _path_2_root_inst_split_path(path: list, has_root_instr: set, p: Project):
    """
    transform a normal path to a path separated by root-instruction
    :param path: [id1, id2, ..., idn]
    :param has_root_instr: a set of block_ids which have already been identified to contain root instructions
    :param p: the relative project
    :return: [(id1, id2, ..., idm), (idm+1, ..., idk), ...]
    """
    res = []
    start = 0
    end = 0
    for idx in range(len(path)):
        block_id = path[idx]
        if block_id in has_root_instr or ends_with_root_instr(p.factory.block(block_id)):
            end = idx
            res.append(tuple(path[start:(end + 1)]))
            start = end + 1

    # note that the last ri_block usually ends with return (ret is a root inst)
    if start <= end:
        res.append(tuple(path[start:(end + 1)]))
    return res


def _rebuild_simple_cfg_by_ri_paths(lips):
    scfg = SimpleCFG()
    # initialize the root by a start empty node
    root_node = SimpleCFGNode(0, is_call=False)
    scfg.root = 0
    scfg.add_node(root_node)
    for lip in lips:
        # is_call is useless here (we may remove it)
        scfg.add_node(SimpleCFGNode(block_id=lip[0], is_call=False))
        scfg.add_child_to(0, lip[0])
        for idx in range(1, len(lip)):
            cur_node = SimpleCFGNode(block_id=lip[idx], is_call=False)
            scfg.add_node(cur_node)
            scfg.add_child_to(lip[idx - 1], lip[idx])
    return scfg


@contextmanager
def _time_limit_for_a_func(seconds, func_entry):
    def signal_handler(signum, frame):
        raise TimeoutForCollectingInfoException(func_entry)

    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)


def len_ri_path(path):
    length = 0
    for b in path:
        length += len(b)
    return length


def prepare_binary_database(p: angr.Project):
    database_dir = p.filename + '_functions'
    if not os.path.isdir(database_dir):
        cmd = './collect_functions.sh %s' % p.filename
        os.system(cmd)
        if not os.path.isdir(database_dir):
            raise Exception('failed to generate database for %s' % p.filename)

    database_dir += '_refs'
    if not os.path.isdir(database_dir):
        cmd = './collect_functions_refs.sh %s' % p.filename
        os.system(cmd)
        if not os.path.isdir(database_dir):
            raise Exception('failed to generate database for %s' % p.filename)
    return p.filename + '_functions'


def func_cfg_file_to_addr(file_name: str):
    assert file_name.endswith('.json')
    return int(file_name[:-5], 16)


class RootInstCFGBuilder:
    """
    we build the CFG based on root instructions according to the SimpleCFG based on basic blocks
    Every element of RI-CFG is a trace of block_id's,
    from the beginning of a function to the 1st block with root instructions, or
    from a block following a root instruction to the next block with root instruction
    """

    def __init__(self, p: angr.Project, cfg=None, database_dir=None):
        self.p = p
        self.cfg = cfg
        # if self.cfg is None:
        #     self.cfg = p.analyses.CFGFast()
        self.database_dir = database_dir

        if self.database_dir is None:
            self.database_dir = prepare_binary_database(self.p)

    def get_all_functions(self):
        """
        only functions in .text section are valid
        """
        text_range = get_section_range(self.p, '.text')
        offset = get_offset(self.p)
        func_entries = set()
        for f in os.listdir(self.database_dir):
            if not f.endswith('.json'):
                continue
            f_addr = func_cfg_file_to_addr(f) + offset
            if f_addr in text_range:
                func_entries.add(f_addr)
        return func_entries

    def _to_root_paths(self, paths, callees: dict, scfg: SimpleCFG, trim=True):
        """
        transform the original paths to paths in the form of root instruction blocks
        :param paths: original paths from simple cfg
        :param callees: the dictionary of callees {call_instr_addr: (callee_entry, arg_addrs: list)}
        :param scfg: the simple cfg
        :param trim: True: remove paths without no return root instructions
        :return:
        """

        # find all blocks which contain root instruction
        # we do not use `call` because sometimes gcc use `jmp` as call, so that a `ret` is reduced
        block_ids = sorted(list(scfg.pool.keys()))
        call_addrs = sorted(list(callees.keys()))
        has_ri = set()
        if len(call_addrs) > 0:
            cur_call_idx = 0
            for idx in range(len(block_ids) - 1):
                if block_ids[idx] <= call_addrs[cur_call_idx] < block_ids[idx + 1]:
                    has_ri.add(block_ids[idx])
                    cur_call_idx += 1
                    if cur_call_idx == len(call_addrs):
                        break
            if cur_call_idx < len(call_addrs) and call_addrs[-1] > block_ids[-1]:
                has_ri.add(block_ids[-1])

        ri_paths = []
        for path in paths:
            tmp = _path_2_root_inst_split_path(path, has_ri, self.p)
            if (trim and len(tmp) > 1) or not trim:
                # there is at least a no return root instruction
                ri_paths.append(tmp)
        return ri_paths

    def build_func_basic_block_level_simple_cfg(self, func_entry):
        offset = get_offset(self.p)
        # for position independent binary, the offset is the load offset of the project
        func_data = '0x%x.json' % (func_entry - offset)
        func_data_path = os.path.join(self.database_dir, func_data)
        scfg, callees, num_callee, _ = load_ida_flowchart_as_simple_cfg(func_data_path, self.p)
        return scfg, callees, num_callee

    def build_func_ri_lips_and_cfg(self, func_entry, max_paths=10000):
        scfg, callees, num_callee = self.build_func_basic_block_level_simple_cfg(func_entry)
        assert len(scfg.pool) > 1
        # scfg = build_simple_cfg(func_entry, self.cfg)

        # check whether there is a call
        has_call = len(callees) > 0

        scfg.label_all_leaf()
        if has_call and len(scfg.pool) > 50:
            # there are too many basic blocks in this functions. To accelerate the process, we trim the cfg.
            scfg.trim()

        lips = scfg.get_linearly_independent_path_BFS(max_paths=max_paths)
        lips = self._to_root_paths(lips, callees, scfg, trim=False)
        scfg = _rebuild_simple_cfg_by_ri_paths(lips)
        return lips, scfg, num_callee, callees

    def get_all_ribs_info(self, func_entry):
        init_state = self.p.factory.blank_state(addr=func_entry, plugins={'ri': RootInstPlugin()})
        root_inst_tech = RootInstTech(func_entry, self.p)
        mgr = self.p.factory.simgr(init_state, techniques=[root_inst_tech])
        mgr.run()
        return root_inst_tech.visited_ribs

    def get_everything_by_symbolic_execution(self, func_entry, max_paths=10000):
        """
        here we build the cfg by symbolic execution directly
        the formulas of every root-instruction-based block will be collected at the same time
        :param func_entry: the entry address of the function to be analyzed
        :return: lips, simple_cfg, formulas dictionary {root-instruction-based block: [formulas]}
        """
        init_state = self.p.factory.blank_state(addr=func_entry, plugins={'ri': RootInstPlugin()})
        root_inst_tech = RootInstTech(func_entry, self.p)
        mgr = self.p.factory.simgr(init_state, techniques=[root_inst_tech])
        mgr.run()
        lips = root_inst_tech.simple_cfg.get_linearly_independent_path_BFS(max_paths=max_paths)

        callee_set = set()
        for b_id, n in root_inst_tech.simple_cfg.pool.items():
            if n.is_call:
                block = self.p.factory.block(b_id)
                last_inst = get_block_last_insn(block)
                callee_set.add(last_inst.op_str)  # it should be the str of a 16-bit function address
        num_callee = len(callee_set)
        return lips, root_inst_tech.simple_cfg, num_callee, root_inst_tech.visited_ribs

    def get_continuous_info_by_symbolic_execution(self, func_entry, fe: FormulaExtractor, max_depth=10):
        offset = get_offset(self.p)
        func_data = '0x%x.json' % (func_entry - offset)
        func_data_path = os.path.join(self.database_dir, func_data)
        scfg, callees, num_callee, _ = load_ida_flowchart_as_simple_cfg(func_data_path, self.p)
        scfg.label_all_leaf()
        if len(callees.keys()) > 1 and len(scfg.pool) > 50:
            # there are too many basic blocks in this functions. To accelerate the process, we trim the cfg.
            scfg.trim()

        tech = ContinuousInfoTech(func_entry, self.p, fe, scfg, callees, max_depth)
        init_state = tech.create_init_state()
        mgr = self.p.factory.simgr(init_state, techniques=[tech])
        try:
            with _time_limit_for_a_func(300, func_entry):
                mgr.run()
        except TimeoutForCollectingInfoException as e:
            log.error(str(e))
        except angr.AngrError as e:
            log.error('meet angr error: ' + str(e))
        except Exception as e:
            log.error('meet error: ' + str(e))
        # merge formulas and constraints of all lips which reaches rib
        tech.merge_rib_formulas_and_constraints()
        # if log.level <= 10:
        #     for lip in tech.ri_lips:
        #         for ends_idx in range(1, len(lip)):
        #             log.debug(tech.fe._visited_smt[lip[:ends_idx]])
        # for a in tech.fe._visited.items():
        #     print(a)

        scfg = _rebuild_simple_cfg_by_ri_paths(tech.ri_lips)
        return tech.ri_lips, scfg, num_callee, callees

# if __name__ == '__main__':
#     p = load_proj('samples/coreutils_O0/true', False)
#     fe = FormulaExtractor(p)
#     cfg = p.analyses.CFGFast()
#     builder = RootInstCFGBuilder(p, cfg)
#
#     builder.get_continuous_info_by_symbolic_execution(cfg.functions['main'].addr, fe)
#
#     lips, _, _, _ = builder.build_func_ri_lips_and_cfg(cfg.functions['main'].addr)
#     for lip in lips:
#         print(lip)

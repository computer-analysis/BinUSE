import json
import random
from copy import deepcopy

from angr import Project

from src.utils import *


class SimpleCFGNode:

    def __init__(self, block_id, is_call, ret_to=None, is_leaf=False):
        self.id = block_id
        self.parents = set()
        self.children = set()
        self.is_call = is_call
        self.is_leaf = is_leaf
        self.ret_to = None
        if self.is_call:
            assert ret_to is not None
            self.ret_to = ret_to

    def add_parent(self, block_id):
        self.parents.add(block_id)

    def add_child(self, block_id):
        self.children.add(block_id)

    def clear_neighbor(self):
        self.parents.clear()
        self.children.clear()

    def copy_without_edges(self):
        new_node = SimpleCFGNode(self.id, self.is_call, self.ret_to, self.is_leaf)
        return new_node

    def set_leaf(self, is_leaf):
        self.is_leaf = is_leaf


class SimpleCFG:

    def __init__(self):
        # we initialize the root node, it is a unreal node, merely representing tree root
        self.root = 0
        self.pool = {0: SimpleCFGNode(0, False)}

    @staticmethod
    def create_a_node(block_id, angr_cfg):
        # merely store all blocks in the function in cur_path
        # all callees are ignored
        # but mark the block is_call True or False
        angr_node = angr_cfg.model.get_any_node(block_id)
        assert angr_node is not None, str(block_id)
        if angr_node.block is None:
            return None
        last_insn = get_block_last_insn(angr_node.block)
        if 'call' in last_insn.mnemonic:
            # jmp to the next instruction
            return_addr = last_insn.address + last_insn.size
            cfg_node = SimpleCFGNode(angr_node.block_id, True, ret_to=return_addr)
        elif 'ret' in last_insn.mnemonic:
            cfg_node = SimpleCFGNode(angr_node.block_id, False, is_leaf=True)
        else:
            cfg_node = SimpleCFGNode(angr_node.block_id, False)
        return cfg_node

    def add_node(self, node: SimpleCFGNode):
        if not self.has_block(node.id):
            self.pool[node.id] = node

    def has_block(self, block_id) -> bool:
        return block_id in self.pool

    def get_node(self, block_id: int) -> SimpleCFGNode:
        return self.pool[block_id]

    def add_child_to(self, block_id: int, child_id: int):
        self.pool[block_id].add_child(child_id)
        self.pool[child_id].add_parent(block_id)

    def _node2str(self, block_id: int, indent=0):
        res = '\t' * indent + str(block_id)
        if len(self.pool[block_id].children) == 0:
            res += ' leaf\n'
        else:
            res += '\n'
            for child_id in self.pool[block_id].children:
                res += self._node2str(child_id, indent + 1)
        return res

    def size(self):
        return len(self.pool)

    def __str__(self):
        # this method may cause infinite recursive
        return self._node2str(self.root, 0)

    def get_all_linearly_independent_paths(self, max_paths=1e10):
        # from the root, traverse all nodes by DFS, but avoid repeated nodes in one path
        paths = []
        cur_path = []
        cur_nodes = set()
        stack = [(self.root, 0)]
        while stack:
            cur_id, father_path_len = stack.pop()
            # avoid repeated nodes in current path
            if cur_id in cur_nodes:
                continue
            cur_path = cur_path[:father_path_len]
            cur_nodes = set(cur_path)
            assert len(cur_path) == len(cur_nodes)
            cur_path.append(cur_id)

            if len(self.pool[cur_id].children) > 0:
                path_len = len(cur_path)
                for child_id in self.pool[cur_id].children:
                    stack.append((child_id, path_len))
            else:
                # no child, it is a leaf, the path has ended
                # the cur_path[0] is 0, remove it from path
                paths.append(cur_path[1:])
                if len(paths) >= max_paths:
                    print('warning: reach paths max limit, exit lip collection process')
                    break
        return paths

    def get_linearly_independent_path_BFS(self, max_paths=10000):
        # Since root is always 0, we skip it
        finished_paths = []
        paths = [[s] for s in self.pool[0].children]
        while (len(paths) + len(finished_paths)) < max_paths and len(paths) != 0:
            new_paths = []
            for p in paths:
                if len(self.pool[p[-1]].children) > 0:
                    has_valid_suc = False
                    for child in self.pool[p[-1]].children:
                        if child in p:
                            continue
                        has_valid_suc = True
                        new_paths.append(p + [child])
                    if not has_valid_suc:
                        # ends with loop or ...
                        finished_paths.append(p)
                else:
                    finished_paths.append(p)
            paths = new_paths
        # here we may have all paths having been finished, or reach the path number limit
        if len(paths) > 0 and len(finished_paths) < max_paths:
            # here we extend each path until it ends, every path merely selects successors in random
            paths = paths[:max_paths - len(finished_paths)]
            for p in paths:
                while True:
                    if len(self.pool[p[-1]].children) == 0:
                        finished_paths.append(p)
                        break
                    random_suc_id = random.choice(list(self.pool[p[-1]].children))
                    if random_suc_id in p:
                        random_suc_id = None
                        # search for the first none-repeated successor
                        for child in self.pool[p[-1]].children:
                            if child not in p:
                                random_suc_id = child
                                break
                        if random_suc_id is None:
                            finished_paths.append(p)
                            break
                    # add the successor
                    p.append(random_suc_id)
        return finished_paths

    def trim(self):
        """
        trim branches without root-instruction (return is not root instruction)
        """
        leaves = []
        for b_id, node in self.pool.items():
            if node.is_leaf and not node.is_call:
                leaves.append(b_id)
        # use leaves to get its last call, then remove these branches
        while len(leaves) > 0:
            leaf = leaves.pop()
            try:
                for parent in self.pool[leaf].parents:
                    # we remove the leaf node from its children set first
                    self.pool[parent].children.remove(leaf)
                    # call is the root instruction, we do not trim it.
                    if self.pool[parent].is_call:
                        continue
                    # if parent has no child, it is a leaf node. We add it to leaves.
                    if len(self.pool[parent].children) == 0:
                        leaves.append(parent)
                self.pool.pop(leaf)
            except KeyError:
                pass

    def label_all_leaf(self):
        for b_id, node in self.pool.items():
            if len(node.children) == 0:
                node.set_leaf(True)


def build_simple_cfg(starting_block, cfg, exit_addrs=None):
    """
    build a simple CFG whose root is the starting block
    :param starting_block: the id of the starting block
    :param cfg: the cfg of this project
    :param exit_addrs: a set of addresses, if one of them is added into a path, the path ends.
    :return: a list of paths, every path is a list of block_ids, and all block_ids which are marked as call blocks
    """
    scfg = SimpleCFG()
    start_node = scfg.create_a_node(starting_block, cfg)
    scfg.add_node(start_node)
    scfg.add_child_to(0, start_node.id)
    stack = [cfg.model.get_any_node(starting_block)]
    while stack:
        node = stack.pop()
        # the popped out node should have already been added to the simple cfg
        assert node.block_id in scfg.pool
        # the block has return instruction, end the path directly
        if scfg.pool[node.block_id].is_leaf:
            continue

        if exit_addrs is not None and node.block_id in exit_addrs:
            continue

        if scfg.get_node(node.block_id).is_call:
            # the successor is the return to block
            suc = cfg.model.get_any_node(scfg.get_node(node.block_id).ret_to)
            if suc:
                if suc.block_id not in scfg.pool:
                    stack.append(suc)
                    suc_node = scfg.create_a_node(suc.block_id, cfg)
                    scfg.add_node(suc_node)
                scfg.add_child_to(node.block_id, suc.block_id)
            else:
                print('invalid return to address 0x%x' % scfg.get_node(node.block_id).ret_to)
        else:
            sucs = cfg.model.get_successors(node)
            for suc in sucs:
                if suc.block_id not in scfg.pool:
                    tmp_n = scfg.create_a_node(suc.block_id, cfg)
                    if tmp_n is None:
                        # I do not know how a node in CFG can have no block
                        continue
                    stack.append(suc)
                    scfg.add_node(tmp_n)
                scfg.add_child_to(node.block_id, suc.block_id)

    return scfg


def _angr_bb_to_simple_cfg_node(bb, callees):
    if len(bb.capstone.insns) == 0:
        # some unknown errors of ida pro
        return SimpleCFGNode(bb.addr, is_call=False)
    last_inst = get_block_last_insn(bb)
    if last_inst.address in callees.keys():
        return SimpleCFGNode(bb.addr, is_call=True, ret_to=bb.addr + bb.size)
    elif is_ret_instr(last_inst):
        return SimpleCFGNode(bb.addr, is_call=False, is_leaf=True)
    else:
        return SimpleCFGNode(bb.addr, is_call=False)


def _ida_bb_to_scfg_nodes(ida_bb: dict, p: Project, offset, callees):
    cur_bb = p.factory.block(ida_bb['start'] + offset)
    bbs = []
    while cur_bb.addr + cur_bb.size < ida_bb['end'] + offset:
        # cur_bb to simple_cfg_node
        bbs.append(_angr_bb_to_simple_cfg_node(cur_bb, callees))
        next_bb_addr = cur_bb.addr + cur_bb.size
        cur_bb = p.factory.block(next_bb_addr)
    if cur_bb.addr + cur_bb.size > ida_bb['end'] + offset:
        cur_bb = p.factory.block(cur_bb.addr, size=ida_bb['end'] + offset - cur_bb.addr)
    bbs.append(_angr_bb_to_simple_cfg_node(cur_bb, callees))
    return bbs


def _process_callees_json(callees, offset):
    callee_set = set()
    new_callees = dict()  # original keys of callees are strings, we convert it to int and add offset
    for inst_addr, callee in callees.items():
        callee_set.add(callee[0])
        callee_entry, arg_addrs = callee
        callee_entry += offset
        if arg_addrs:
            arg_addrs = list(map(lambda a: a + offset, arg_addrs))
        new_callees[int(inst_addr) + offset] = (callee_entry, arg_addrs)
    num_callee = len(callee_set)
    return new_callees, num_callee


def load_ida_flowchart_as_simple_cfg(chart_file, p: Project):
    """
    :param chart_file: the json file of this function
    :param p: the project object
    :return:
    scfg: simple cfg of basic blocks
    callees: a dictionary of callees, (instruction_addr, (callee_entry, arg_instruction_addr))
    num_callee: number of different callees (callee_entry)
    func_addr: the entry of this function
    """
    offset = get_offset(p)
    with open(chart_file, 'r') as cf:
        data = json.load(cf)
        chart = data['cfg']
        func_addr = data['func_addr']
        callees, num_callee = _process_callees_json(data['callees'], offset)
        # by default id 0 is the start block,
        # the ida pro do not split basic blocks by call instruction. we need to adapt the cahrt to angr simple cfg.
        scfg = SimpleCFG()
        bb_map = []
        for ida_bb in chart:
            nodes = _ida_bb_to_scfg_nodes(ida_bb, p, offset, callees)
            bb_map.append(nodes)
            for n in nodes:
                scfg.add_node(n)
            for p_idx in range(len(nodes) - 1):
                scfg.add_child_to(nodes[p_idx].id, nodes[p_idx + 1].id)
        # build the relationship between ida_bb
        for idx in range(len(chart)):
            last_scfg_node = bb_map[idx][-1]
            for suc_idx in chart[idx]['succs']:
                scfg.add_child_to(last_scfg_node.id, bb_map[suc_idx][0].id)
        # the root 0 should be connected with the 1st block
        scfg.add_child_to(0, bb_map[0][0].id)
        # some ida_bb is a partial cut of angr_bb, remove these situation
        # for example, expr1 -> expr2 -> expr3 -> je, expr1 can be a single basic block in ida_bb
        # all these node has merely 1 successor
        for b_id, node in scfg.pool.items():
            if (not node.is_call) and len(node.children) == 1 and b_id != 0:
                suc_addr = list(node.children)[0]
                angr_bb = p.factory.block(b_id)
                angr_bb_range = range(angr_bb.addr, angr_bb.addr + angr_bb.size)
                if suc_addr in angr_bb_range:
                    # angr_bb larger than ida_bb
                    node.children.clear()
                    _tmp_loop_count = 0
                    while (not scfg.pool[suc_addr].is_call) and len(scfg.pool[suc_addr].children) == 1 \
                            and suc_addr in angr_bb_range and (suc_addr not in scfg.pool[suc_addr].children):
                        suc_addr = list(scfg.pool[suc_addr].children)[0]
                        _tmp_loop_count += 1
                        # to jump out from dead loop
                        if _tmp_loop_count > 100:
                            break
                    if suc_addr in angr_bb_range:
                        for child in scfg.pool[suc_addr].children:
                            scfg.add_child_to(b_id, child)
                    else:
                        scfg.add_child_to(b_id, suc_addr)
        return scfg, callees, num_callee, func_addr

# import os
#
# if __name__ == '__main__':
#     # chart_file = 'samples/coreutils_O0/cat_functions/0x274e.json'
#     database_dir = 'samples/coreutils_O1/nl_functions'
#     p = load_proj('samples/coreutils_O1/nl', False)
#
#     # chart_file = 'samples/coreutils_O2/cat_functions/0x1980.json'
#     # database_dir = 'samples/coreutils_O2/cat_functions'
#     # p = load_proj('samples/coreutils_O2/cat', False)
#
#     text_range = get_section_range(p, '.text')
#     offset = get_offset(p)
#     distribution = dict()
#     for chart_file in os.listdir(database_dir):
#         if not chart_file.endswith('json'):
#             continue
#         entry = int(chart_file[:-5], 16)
#         if (entry + offset) not in text_range:
#             continue
#         chart_file = os.path.join(database_dir, chart_file)
#         scfg, callees, _ = load_ida_flowchart_as_simple_cfg(chart_file, p)
#         scfg.label_all_leaf()
#         if len(scfg.pool) > 50:
#             scfg.trim()
#
#         callee_set = set()
#         for inst_addr, callee in callees.items():
#             callee_set.add(callee)
#         num_call = len(callee_set)
#         if num_call in distribution.keys():
#             distribution[num_call] += 1
#         else:
#             distribution[num_call] = 1
#     print(distribution)

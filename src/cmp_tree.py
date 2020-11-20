from itertools import permutations

import claripy
import zss

from src.utils import in_ranges


def expr2tree(e, exe_ranges, data_ranges):
    if isinstance(e, int) or isinstance(e, float):
        return zss.Node(label=e)
    elif isinstance(e, claripy.bv.BVV):
        value = e.value
        if in_ranges(value, exe_ranges):
            return zss.Node(label='exe_ptr')
        elif in_ranges(value, data_ranges):
            return zss.Node(label='data_ptr')
        else:
            return zss.Node(label=value)
    elif isinstance(e, claripy.ast.base.Base):
        if e.depth == 1:
            if isinstance(e, claripy.Bits):
                if e.symbolic:
                    # return zss.Node(label='vs' + str(e.size()))
                    return zss.Node(label=str(e))
                elif isinstance(e, claripy.ast.bv.BV):
                    # here will receive all constants
                    # we separate all constants value to 3 types:
                    # executable_pointer, data_pointer, and normal constant
                    value = e.args[0]
                    if in_ranges(value, exe_ranges):
                        return zss.Node(label='exe_ptr')
                    elif in_ranges(value, data_ranges):
                        return zss.Node(label='data_ptr')
                    else:
                        return zss.Node(label=e.args[0])
                else:
                    return zss.Node(label=str(e))
            elif isinstance(e, claripy.ast.bool.Bool):
                if e.symbolic:
                    return zss.Node(label='bs')
                else:
                    return zss.Node(label='b')
            else:
                assert False, 'unknown base type %s' % e.__class__
        elif e.depth == 2 and e.op == 'Extract':
            # this is also a leaf of AST
            return zss.Node(label=str(e.args[2]))
        elif e.op == 'Concat':
            # we ignore all concat 0 at head
            tmp1 = expr2tree(e.args[0], exe_ranges, data_ranges)
            if tmp1.label == 0:
                return expr2tree(e.args[1], exe_ranges, data_ranges)
            else:
                node = zss.Node(label=e.op)
                node.addkid(tmp1)
                node.addkid(expr2tree(e.args[1], exe_ranges, data_ranges))
                return node
        else:
            # if isinstance(e, claripy.ast.bv.BV) and e.depth == 2 and e.symbolic and e.op == 'Extract':
            #     return zss.Node(label='vs' + str(e.size()))
            # else:
            node = zss.Node(label=e.op)
            for arg in e.args:
                node.addkid(expr2tree(arg, exe_ranges, data_ranges))
            return node
    else:
        assert False, 'unknown type %s' % e.__class__


def _replace_tree_node(t, replace_map: dict):
    stack = [t]
    while stack:
        n = stack.pop()
        if n.label in replace_map.keys():
            n.label = replace_map[n.label]
        else:
            if n.children:
                stack.extend(n.children)


def copy_zss_tree_with_replacement(t: zss.Node, replace_map: dict, max_depth=10):
    # deepcopy is very slow, it becomes bottleneck
    children = list()
    if max_depth > 0 and len(t.children) > 0:
        for c in t.children:
            children.append(copy_zss_tree_with_replacement(c, replace_map, max_depth - 1))
    if t.label in replace_map.keys():
        root = zss.Node(label=replace_map[t.label], children=children)
    else:
        root = zss.Node(label=t.label, children=children)
    return root


def copy_zss_tree_with_replacement_no_recursion(t: zss.Node, replace_map: dict):
    if t.label in replace_map.keys():
        root = zss.Node(label=replace_map[t.label])
    else:
        root = zss.Node(label=t.label)
    stack = [(c, 1) for c in reversed(t.children)]
    cur_path = [root]
    while len(stack) > 0:
        tmp, depth = stack.pop()
        if len(tmp.children) > 0:
            cur_depth = len(cur_path)
            for c in reversed(tmp.children):
                stack.append((c, cur_depth))

        cur_path = cur_path[:depth]
        if tmp.label in replace_map.keys():
            new_node = zss.Node(label=replace_map[tmp.label])
        else:
            new_node = zss.Node(label=tmp.label)
        cur_path[-1].addkid(new_node)
        cur_path.append(new_node)
    return root


def _eq_tree(t1: zss.Node, t2: zss.Node):
    s1 = [t1]
    s2 = [t2]
    while len(s1) > 0 and len(s2) > 0:
        tmp1 = s1.pop()
        tmp2 = s2.pop()
        if tmp1.label == tmp2.label and len(tmp1.children) == len(tmp2.children):
            s1.extend(tmp1.children)
            s2.extend(tmp2.children)
        else:
            return False
    return True


def get_tree_used_input(t, input):
    used = set()
    stack = [t]
    while stack:
        n = stack.pop()
        if n.label in input:
            used.add(n.label)
        else:
            if n.children:
                stack.extend(n.children)
    return list(used)


def tree_equal(t1, t2, _input1, _input2):
    """
    compare 2 trees, return t1 == t2
    :param t1: a tree (zss root node)
    :param t2: ...
    :param _input1: a set of all labels (str) which represent input symbols
    :param _input2: ...
    :return: a bool, t1 == t2
    """
    t1_input = get_tree_used_input(t1, _input1)
    t2_input = get_tree_used_input(t2, _input2)

    if len(t1_input) != len(t2_input):
        # tentatively we treat expressions with different number of inputs as different, we do not prove
        return False

    for per_t1_input_idx in permutations(range(len(t1_input))):
        replace_map = {t2_input[i]: t1_input[per_t1_input_idx[i]] for i in range(len(per_t1_input_idx))}
        # tmp_t2 = deepcopy(t2)
        # _replace_tree_node(tmp_t2, replace_map)
        tmp_t2 = copy_zss_tree_with_replacement(t2, replace_map)
        # tmp_t2 = copy_zss_tree_with_replacement_no_recursion(t2, replace_map)
        # print('t1')
        # print(str(t1))
        # print('t2')
        # print(str(tmp_t2))
        # print()

        if _eq_tree(t1, tmp_t2):
            return True
    return False


def tree_distance(t1, t2, _input1, _input2):
    """
        compare 2 trees, return t1 == t2
        :param t1: a tree (zss root node)
        :param t2: ...
        :param _input1: a set of all labels (str) which represent input symbols
        :param _input2: ...
        :return: a bool, t1 == t2
        """
    t1_input = get_tree_used_input(t1, _input1)
    t2_input = get_tree_used_input(t2, _input2)

    if len(t1_input) != len(t2_input):
        # tentatively we treat expressions with different number of inputs as different, we do not prove
        return False

    min_distance = 1000000
    for per_t1_input_idx in permutations(range(len(t1_input))):
        replace_map = {t2_input[i]: t1_input[per_t1_input_idx[i]] for i in range(len(per_t1_input_idx))}
        # tmp_t2 = deepcopy(t2)
        # _replace_tree_node(tmp_t2, replace_map)
        tmp_t2 = copy_zss_tree_with_replacement(t2, replace_map)
        # tmp_t2 = copy_zss_tree_with_replacement_no_recursion(t2, replace_map)
        # print('t1')
        # print(str(t1))
        # print('t2')
        # print(str(tmp_t2))
        # print()
        tmp_d = zss.simple_distance(t1, tmp_t2)
        min_distance = min(min_distance, tmp_d)
    return min_distance

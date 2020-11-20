import json
import os

from idaapi import *
from idautils import *
from idc import *


def list_func_entries():
    res = dict()
    func_map = dict()
    total_func_addr_set = set()
    for seg_ea in Segments():
        res[seg_ea] = []
        for func_ea in Functions(seg_ea, SegEnd(seg_ea)):
            total_func_addr_set.add(func_ea)
            func_name = GetFunctionName(func_ea)
            for _ in Chunks(func_ea):
                # we only collect functions with instructions
                res[seg_ea].append(func_ea)
                func_map[func_ea] = func_name
                break
    return res, func_map, total_func_addr_set


def get_xrefs_froms(addr):
    xrefs = XrefsTo(addr)
    from_set = set()
    for xref in xrefs:
        from_set.add(xref.frm)
    return from_set


def get_funtion_callers(func_entry, total_func_addr_set):
    # we try to find caller function which refers to the function entry
    # the caller may use the callee as a data
    def find_caller_helper(from_address, deref_iter):
        # return a set of function entries
        deref_iter += 1
        if deref_iter > 10:
            # the upper bound on times of dereference
            return set()
        possible_caller = GetFunctionAttr(from_address, FUNCATTR_START)
        if possible_caller in total_func_addr_set:
            return {possible_caller}
        # we need to de-refer this address
        tmp_from_set = get_xrefs_froms(from_address)
        callers = set()
        for tmp_from in tmp_from_set:
            callers.update(find_caller_helper(tmp_from, deref_iter))
        return callers

    from_set = get_xrefs_froms(func_entry)
    if len(from_set) == 0:
        print('no caller can be found for 0x%x' % func_entry)

    caller_entries = set()
    for ref_from in from_set:
        caller_entries.update(find_caller_helper(ref_from, 0))
    return caller_entries


def main(output_dir):
    if not os.path.isdir(output_dir):
        os.mkdir(output_dir)
    _, func_map, total_func_addr_set = list_func_entries()

    # write function map file
    func_map_file = os.path.join(output_dir, 'func_map')
    with open(func_map_file, 'w') as fmf:
        content = ''
        for addr_func in func_map.items():
            content += '0x%x : %s\n' % addr_func
        fmf.write(content)

    for func_addr in total_func_addr_set:
        callers = get_funtion_callers(func_addr, total_func_addr_set)
        output_file = os.path.join(output_dir, '0x%x.json' % func_addr)
        with open(output_file, 'w') as f:
            json.dump(list(callers), f)


if __name__ == '__main__':
    output_dir = ARGV[1]
    main(output_dir)
    qexit()

"""
We currently only try to extract the input for a x86 lib call
"""
from src.utils import *
import os
import json
from src.simple_cfg import _process_callees_json


def get_func_callee_info(func_entry, p: angr.Project):
    """
    Different the interface of root_instrs.py, we merely get the callee dictionary of this function
    """
    offset = get_offset(p)
    func_info_path = os.path.join(p.filename + '_functions', "0x%x.json" % (func_entry - offset))
    with open(func_info_path, 'r') as f:
        func_info = json.load(f)
        callees = func_info['callees']
        callees, _ = _process_callees_json(callees, offset)
        return callees


def analyze_x86_cc_callee_args(func_entry, p: angr.Project, valid_callees: set = None):
    """
    This function is used to analyze the input arguments (following the x86 calling convention) and their size
    all args being analyzed of a callee should be pushed into stack
    :param func_entry:
    :param p:
    :param valid_callees: we use this to show valid callees (usually lib calls currently)
    :return:
    """
    callees = get_func_callee_info(func_entry, p)
    callee_arg_dict = dict()
    for call_instr, info in callees.items():
        callee_entry = info[0]
        callee_arg_addrs = info[1]
        if callee_arg_addrs is None or len(callee_arg_addrs) == 0:
            # no args callee
            continue
        if valid_callees and callee_entry not in valid_callees:
            # not a callee supposed to be analyzed
            continue
        arg_sizes = []
        while len(arg_sizes) < len(callee_arg_addrs):
            min_addr = min(callee_arg_addrs)
            block = p.factory.block(addr=min_addr)
            for insn in block.capstone.insns:
                # note here the arg_addrs are in ascending order, the position of args on stack should be reversed later
                if insn.insn.address in callee_arg_addrs:
                    callee_arg_addrs.remove(insn.insn.address)
                    if insn.insn.mnemonic == 'push':
                        # there should be only 1 operand
                        arg_sizes.append(insn.insn.operands[0].size)
                    elif insn.insn.mnemonic == 'mov' and insn.insn.op_str.startswith('dword ptr [esp]'):
                        # this is equivalent to push 32bits
                        arg_sizes.append(4)
                    else:
                        # corner case, just add a 4 bytes
                        log.warning('Werid arguments pass instruction 0x%x %d %s %s' %
                                    (insn.insn.address, insn.insn.size, insn.insn.mnemonic, insn.insn.op_str))
                        arg_sizes.append(4)
        # we need to transform the size list to the offset list
        # remember the arg being pushed at last should at the top
        arg_offsets = []
        for size in reversed(arg_sizes):
            if len(arg_offsets) == 0:
                arg_offsets.append(size)
            else:
                arg_offsets.append(size + arg_offsets[-1])
        callee_arg_dict[callee_entry] = arg_offsets
    return callee_arg_dict


def get_libcall_args(libcall_entries: dict, all_text_func: set, p: angr.Project):
    callee_arg_dict = dict()
    for func_entry in all_text_func:
        # if p.arch.name == 'X86'
        tmp = analyze_x86_cc_callee_args(func_entry, p, set(libcall_entries.keys()))
        # merge tmp with callees which has been analyzed
        # there may be some conflicts
        for entry, arg_offsets in tmp.items():
            if entry in callee_arg_dict:
                if arg_offsets != callee_arg_dict[entry]:
                    log.error('Conflict on callee of 0x%x (%s)' % (entry, libcall_entries[entry]))
                    # use the longest one
                    if len(arg_offsets) > len(callee_arg_dict[entry]):
                        callee_arg_dict[entry] = arg_offsets
            else:
                callee_arg_dict[entry] = arg_offsets
    # change entry to function names
    new_callee_arg_dict = dict()
    for entry in callee_arg_dict.keys():
        new_callee_arg_dict[libcall_entries[entry]] = callee_arg_dict[entry]
    return new_callee_arg_dict

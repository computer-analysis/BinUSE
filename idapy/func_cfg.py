import json
import os

from idaapi import *
from idautils import *
from idc import *


def get_func_cfg(func_addr):
    func_ptr = get_func(func_addr)
    return FlowChart(func_ptr)


def cfg_to_dict(cfg, addr, func_set):
    # the func_set is used to solve jmp-to-a-function situations
    callees = dict()  # {inst_addr: callee_name}
    cfg_nodes = [None for _ in range(cfg.size)]
    for b in cfg:
        cfg_nodes[b.id] = {'start': b.start_ea, 'end': b.end_ea,
                           'preds': [pre.id for pre in b.preds()],
                           'succs': [suc.id for suc in b.succs()]}
    # the last basic block may not be valid in some cases, and it has no instructions
    last_idx = len(cfg_nodes) - 1
    if cfg_nodes[last_idx]['start'] == cfg_nodes[last_idx]['end']:
        # it is invalid, remove it from all nodes' succs
        for idx in range(last_idx):
            if last_idx in cfg_nodes[idx]['succs']:
                cfg_nodes[idx]['succs'].remove(last_idx)
        cfg_nodes = cfg_nodes[:last_idx]

    # collect callees
    for (start, end) in Chunks(addr):
        for head in Heads(start, end):
            instr = GetDisasm(head)
            if instr.startswith('call') or instr.startswith('j') or instr.startswith('BL'):
                # sometimes the fuction uses jmp to call a function (skip a ret instruction)
                for xref in XrefsFrom(head, 0):
                    if xref.to in func_set:
                        # callees[head] = xref.to
                        # sometimes ida pro fails to analyze he arguments of a function call, we use all
                        # registers being written as formulas
                        arg_addrs = get_arg_addrs(head)
                        # the arg_addrs is a list of addresses of instructions where the arguments are initialized
                        callees[head] = (xref.to, arg_addrs)
                    # print(xref.type, XrefTypeName(xref.type), 'from', hex(xref.frm), 'to', hex(xref.to))

    return {'func_addr': addr, 'callees': callees, 'cfg': cfg_nodes}


def save_json(d, output):
    with open(output, 'w') as f:
        json.dump(d, f, indent=2)


def save_func_to_json(func_addr, output, func_set):
    cfg = get_func_cfg(func_addr)
    # print 'get flow chart %s' % str(cfg)
    d = cfg_to_dict(cfg, func_addr, func_set)
    save_json(d, output)


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


def main(output_dir):
    if not os.path.isdir(output_dir):
        os.mkdir(output_dir)
    seg_funcs, func_map, total_func_set = list_func_entries()
    func_map_file = os.path.join(output_dir, 'func_map')
    with open(func_map_file, 'w') as fmf:
        content = ''
        for addr_func in func_map.items():
            content += '0x%x : %s\n' % addr_func
        fmf.write(content)

    for seg, funcs in seg_funcs.items():
        for func_ea in funcs:
            save_func_to_json(func_ea, os.path.join(output_dir, '0x%x.json' % func_ea), total_func_set)


if __name__ == '__main__':
    # use idc.ARGV to pass script parameters
    output_dir = ARGV[1]
    main(output_dir)
    qexit()

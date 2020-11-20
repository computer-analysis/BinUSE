# -*- coding: utf-8 -*-
"""
Read the output info file and dump it to disk
"""
import os
import sys
import pickle


def process_info(p, mode='dict'):
    """
    dict mode: an item of this is ('bin1_f_name', {'bin2_f_name1': score1, 'bin2_f_name2': score2, ...})
    list mode: an item of this is ('bin1_f_name', [('bin2_f_name1', score1), ('bin2_f_name2', score2), ...])
    return: a dict formed by above items
    """
    res = {}
    # number of false negative (the similarity of this function to its counterpart should be > 0, but not)
    with open(p) as f:
        lines = f.readlines()
        next_line_invalid = False
        for l in lines:
            if next_line_invalid:
                next_line_invalid = False
                continue
            if l.startswith("Match"):
                continue
            if 'finds no counterpart' in l:
                next_line_invalid = True
                continue
            elif "[" in l:
                # this is it
                items = l.split(":")
                func_name = items[0].strip()
                lstring = items[1]
                ll = eval(lstring.strip())
                if func_name not in l:
                    # this is possible, function foo in O0 gcc but not in O3 gcc, so we skip it, since there is no ground truth
                    continue
                # filter out all function comparison pair which does not involve solver
                ll = list(filter(lambda l: not isinstance(l[1][1], int), ll))
                if len(ll) == 0:
                    continue
                # we only use the result with a positive score
                ll = list(filter(lambda l: l[1][0] > 0.0, ll))
                if len(ll) == 0:
                    if mode == 'list':
                        res[func_name] = []
                    elif mode == 'dict':
                        res[func_name] = {}
                    else:
                        raise NotImplementedError()
                else:
                    if mode == 'list':
                        res[func_name] = list(map(lambda l: (l[0].strip(), l[1][0]), ll))
                    elif mode == 'dict':
                        tmp = dict()
                        for item in ll:
                            tmp[item[0].strip()] = item[1][0]
                        res[func_name] = tmp
                    else:
                        raise NotImplementedError()
    return res


if __name__ == '__main__':
    info_path = sys.argv[1]
    dump_mode = sys.argv[2]
    binuse_res = process_info(info_path, dump_mode)
    with open(info_path + '.pkl', 'wb') as pkl_dump:
        pickle.dump(binuse_res, pkl_dump)


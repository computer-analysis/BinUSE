# -*- coding: utf-8 -*-
'''
We show how we optimize each result in this file
'''
import os
import sys
import pickle


def optimize(res_use, res_dnn, do_reorder=True, insert_sim_threshold=0.29):
    """
    res_use is the result of BinUSE, dump with dict mode
    res_dnn is the result of DNN-based tech, dump with list mode
    the reture result is the optimized result in list mode
    """
    num_FN = 0
    FN_list = []
    num_use_total = len(res_use.keys())
    for k, v in res_use.items():
        skip_funcs = []
        skip_funcs = set(skip_funcs)
        if k in skip_funcs:
            num_use_total -= 1
            continue
        if k not in res_dnn:
            # this is possible, functions with less than 3 basic blocks will be skipped by DNN
            num_use_total -= 1
            continue
        if True:
            if k not in v.keys():
                num_FN += 1
                FN_list.append(k)

            t = []
            tmp_dnn_matched_set = set()
            for matched_func, dnn_similarity in res_dnn[k]:
                tmp_dnn_matched_set.add(matched_func)
                if matched_func not in v.keys():
                    # if len(v.keys()) > 0 and dnn_similarity < 0.9:
                    #     continue
                    t.append((matched_func, (0.0, dnn_similarity)))
                elif matched_func in v.keys():
                    # in DNN and in USE --> we will just keep it
                    t.append((matched_func, (v[matched_func], dnn_similarity)))
            if do_reorder:
                for matched_func, use_similarity in v.items():
                    if matched_func not in tmp_dnn_matched_set:
                        if v[matched_func] < insert_sim_threshold:
                            continue
                        t.append((matched_func, (use_similarity, 0.0)))
            t = sorted(t, key=lambda i: i[1], reverse=True)
            res_dnn[k] = t
    return res_dnn, num_FN, num_use_total


if __name__ == '__main__':
    use_f = open(sys.argv[1], 'rb')
    dnn_f = open(sys.argv[2], 'rb')
    output_f_path = sys.argv[3]
    res_use = pickle.load(use_f)
    res_dnn = pickle.load(dnn_f)
    res, num_use_FN, num_use_total = optimize(res_use, res_dnn)
    with open(output_f_path, 'wb') as f:
        pickle.dump(res, f)



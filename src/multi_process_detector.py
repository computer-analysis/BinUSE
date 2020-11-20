import multiprocessing
import copy
from src.detector import *
from src.detector import _invalid_difference_value
from src.root_inst.root_inst_cfg import _time_limit_for_a_func

queue = multiprocessing.Queue()


def get_inline_formulas_subprocess(proj_id, proj_path, libcalls, valid_funcs, f_entry):
    proj = load_proj(proj_path)
    fe = FormulaExtractor(proj, None, mode='smt',
                          state_options=(), no_constraints=False,
                          filter_assignment=True)
    log.info('collecting formulas from 0x%x(%s)' % (f_entry, proj.filename))
    tech = StopAtLibCallTech(f_entry, proj, fe, libcalls, valid_funcs)
    simgr = proj.factory.simgr(tech.create_init_state(), techniques=[tech])
    try:
        with _time_limit_for_a_func(600, f_entry):
            simgr.run()
    except TimeoutForCollectingInfoException as e:
        log.error(str(e))
    except Exception as e:
        log.error('Unknown Exception %s at 0x%x %s' % (str(e), f_entry, proj.filename))
    # put cached information to queue
    first_libcall_key = (tech.all_keys, tech.all_lib_calls, tech.merge_path_to_same_lib_call_together())
    for rib in tech.all_keys:
        if rib not in fe._visited:
            fe._visited[rib] = None
        if rib not in fe._visited_smt:
            fe._visited_smt[rib] = None
    queue.put((proj_id, f_entry, first_libcall_key, fe._visited_smt, fe._visited))


def prepare_inline_formula_multi_process(detector, proj_ids=(0, 1)):
    # iterate all function entries
    args = []
    for proj_id in proj_ids:
        for f_entry in detector._valid_funcs[proj_id]:
            tmp_args = (proj_id, detector._p[proj_id].filename,
                        detector._libcalls[proj_id], detector._valid_funcs[proj_id], f_entry)
            args.append(tmp_args)
    return args
    # with multiprocessing.Pool(process_num) as p:
    #     pool_ret = p.starmap(func=get_inline_formulas_subprocess, iterable=args, chunksize=1)


def after_inline_formula_multi_process(detector):
    count = 0
    while not queue.empty():
        proj_id, f_entry, a, b, c = queue.get()
        detector._visited_1st_libcall[proj_id][f_entry] = a
        detector._fe[proj_id]._visited_smt.update(b)
        detector._fe[proj_id]._visited.update(c)
        count += 1
    print('collect successfully %d' % count)


def collect_funcs_formulas_multiprocess(d: Detector, processes, load_fail):
    log.warning('start collocting formulas ...')
    args = prepare_inline_formula_multi_process(d, load_fail)
    print('total # functions: %d' % len(args))
    if len(args) > 0:
        with multiprocessing.Pool(processes) as p:
            p.starmap(func=get_inline_formulas_subprocess, iterable=args, chunksize=1)
            p.close()
            p.join()
        after_inline_formula_multi_process(d)


def _merge_formula_with_constraints(block_id, f_info):
    formulas, constraints, input = f_info[block_id]
    log.debug('formulas    = %s (%s trace %s)' % (str(formulas), f_info['filename'], str(block_id)))
    log.debug('constraints = %s (%s trace %s)' % (str(constraints), f_info['filename'], str(block_id)))
    log.debug('read_from   = %s (%s trace %s)' % (str(input), f_info['filename'], str(block_id)))
    merged_formulas = []
    for f in formulas:
        merged_formulas.append(merge_fe_formulas([(f[1], constraints)], ptr_size=f[1].size())[0])
    log.debug(
        'merged_formulas = %s (%s trace %s)' % (str(merged_formulas), f_info['filename'], str(block_id)))
    return merged_formulas, constraints, input


def _cmp(block0, f0_info, block1, f1_info, symbolic_eq_block_threshold):
    # we merely support smt mode currently
    try:
        merged_f0, c0, in0 = _merge_formula_with_constraints(block0, f0_info)
        merged_f1, c1, in1 = _merge_formula_with_constraints(block1, f1_info)
        if len(merged_f0) > 0 and len(merged_f1) > 0:
            already_matched = set()
            for f0 in merged_f0:
                for f1 in merged_f1:
                    if f1 in already_matched:
                        continue
                    if prove_equal(f0, f1, in0, in1, c0, c1, cmp_limit=120):
                        already_matched.add(f1)
                        break
            if len(already_matched) > 0:
                return len(already_matched) / len(merged_f0)
            else:
                # if no formula matches and the constraints are complex enough, we compare constraints only
                if len(c0) + len(c1) > 2 \
                        and ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1), cmp_limit=120):
                    return symbolic_eq_block_threshold
                else:
                    return 0.0
        else:
            # no formulas are collected, we compare constraints only
            if ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1), cmp_limit=720):
                return symbolic_eq_block_threshold
    except TooManyVariables4Comparison as e:
        # the output of this error could be huge
        log.warning(e.__class__)
    except Exception as e:
        log.error(e)
    return 0.0


def _endswith_libcall(path_trace, libcalls):
    if path_trace[-1] in libcalls.keys():
        return libcalls[path_trace[-1]]
    else:
        return None


def _compare_functions_with_merged_libcalls(merged_args0, merged_args1):
    already_matched_keys = set()
    all_merged_formulas_num = 0
    for libcall_addr0 in merged_args0.keys():
        for v0_name, merged_f0, valid_cons0 in merged_args0[libcall_addr0]:
            all_merged_formulas_num += 1
            for libcall_addr1 in merged_args1.keys():
                tmp_matched = False
                for v1_name, merged_f1, valid_cons1 in merged_args1[libcall_addr1]:
                    if (libcall_addr1, v1_name) in already_matched_keys:
                        continue
                    try:
                        if prove_equal(merged_f0, merged_f1, None, None, [valid_cons0], [valid_cons1],
                                       equal_var=False):
                            already_matched_keys.add((libcall_addr1, v1_name))
                            tmp_matched = True
                            break
                    except TooManyVariables4Comparison as e:
                        log.error(e.__class__)
                if tmp_matched:
                    break
    return already_matched_keys, all_merged_formulas_num


def prepare_f_infos_list(d: Detector, skip_compare_threshold=0.01):
    basic_infos = {'symbolic_eq_block_threshold': d._symbolic_eq_block_threshold,
                   0: {'filename': d._p[0].filename, 'libcalls': d._libcalls[0]},
                   1: {'filename': d._p[1].filename, 'libcalls': d._libcalls[1]}}
    basic_infos[0].update(d._fe[0]._visited)
    basic_infos[1].update(d._fe[1]._visited)
    args = []
    skipped_pairs = []
    for start0 in d._valid_funcs[0]:
        for start1 in d._valid_funcs[1]:
            if start0 not in d._visited_1st_libcall[0]:
                break
            if start1 not in d._visited_1st_libcall[1]:
                continue
            sim = d._inlined_callees_cmp(start0, start1)
            if sim < skip_compare_threshold:
                skipped_pairs.append((start0, start1))
                continue
            tmp = copy.deepcopy(basic_infos)
            tmp[0]['start'] = start0
            tmp[1]['start'] = start1
            tmp[0]['keys'] = d._visited_1st_libcall[0][start0]
            tmp[1]['keys'] = d._visited_1st_libcall[1][start1]
            tmp['sim'] = sim
            args.append(tmp)
    return args, skipped_pairs


def compare_functions(f_infos: dict):
    """
    :param f_infos: a tuple of size 2, with 2 dictionaries
    :return:
    """

    def extract_func_info(idx):
        start = f_infos[idx]['start']
        filename = f_infos[idx]['filename']
        libcalls = f_infos[idx]['libcalls']
        ks, libcalls_this_func, merged_args = f_infos[idx]['keys']
        return start, filename, libcalls, ks, libcalls_this_func, merged_args

    start0, filename0, all_libcalls0, ks0, libcalls0, merged_args0 = extract_func_info(0)
    start1, filename1, all_libcalls1, ks1, libcalls1, merged_args1 = extract_func_info(1)
    sim = f_infos['sim']
    symbolic_eq_block_threshold = f_infos['symbolic_eq_block_threshold']

    if len(ks0) == 0:
        log.warning('no lib call formulas are collected from 0x%x (%s)' % (start0, filename0))
        # raise InvalidFunctionException(start0)
        return

    if len(ks1) == 0:
        log.warning('no lib call formulas are collected from 0x%x (%s)' % (start1, filename1))
        # raise InvalidFunctionException(start1)
        return

    log.info('There are %d LIPs from %s and %d LIPs from %s' % (len(ks0), filename0,
                                                                len(ks1), filename1))

    def merge_formula_with_constraints(block_id, proj_id, filename):
        formulas, constraints, input = f_infos[proj_id][block_id]
        log.debug('formulas    = %s (%s trace %s)' % (str(formulas), filename, str(block_id)))
        log.debug('constraints = %s (%s trace %s)' % (str(constraints), filename, str(block_id)))
        log.debug('read_from   = %s (%s trace %s)' % (str(input), filename, str(block_id)))
        merged_formulas = []
        for f in formulas:
            merged_formulas.append(merge_fe_formulas([(f[1], constraints)], ptr_size=f[1].size())[0])
        log.debug(
            'merged_formulas = %s (%s trace %s)' % (str(merged_formulas), filename, str(block_id)))
        return merged_formulas, constraints, input

    def cmp(block0, block1):
        # we merely support smt mode currently
        try:
            merged_f0, c0, in0 = merge_formula_with_constraints(block0, 0, filename0)
            merged_f1, c1, in1 = merge_formula_with_constraints(block1, 1, filename1)
            if len(merged_f0) > 0 and len(merged_f1) > 0:
                already_matched = set()
                for f0 in merged_f0:
                    for f1 in merged_f1:
                        if f1 in already_matched:
                            continue
                        if prove_equal(f0, f1, in0, in1, c0, c1, cmp_limit=120):
                            already_matched.add(f1)
                            break
                if len(already_matched) > 0:
                    return len(already_matched) / len(merged_f0)
                else:
                    # if no formula matches and the constraints are complex enough, we compare constraints only
                    if len(c0) + len(c1) > 2 \
                            and ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1), cmp_limit=120):
                        return symbolic_eq_block_threshold
                    else:
                        return 0.0
            else:
                # no formulas are collected, we compare constraints only
                if ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1), cmp_limit=720):
                    return symbolic_eq_block_threshold
        except TooManyVariables4Comparison as e:
            # the output of this error could be huge
            log.warning("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                        (str(e.__class__), start0, filename0, start1, filename1))
            # to achieve a low FN, we treat this case as positive
            return symbolic_eq_block_threshold
        except Exception as e:
            log.error("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                      (str(e), start0, filename0, start1, filename1))
        return 0.0

    def endswith_libcall(path_trace, libcalls):
        if path_trace[-1] in libcalls.keys():
            return libcalls[path_trace[-1]]
        else:
            return None

    def similar_libcalls(trace0, trace1):
        call0, call1 = endswith_libcall(trace0, all_libcalls0), endswith_libcall(trace1, all_libcalls1)
        if call0 == call1:
            return True
        if call0 is None or call1 is None:
            # we do not know the exact libcall, just treat them as similar
            return True
        call0 = get_func_names_with_similar_libcall_replacement([call0])
        call1 = get_func_names_with_similar_libcall_replacement([call1])
        if call0 == call1:
            return True
        # '.malloc', '.memset', '.calloc' are special
        mem_opt_funcs = {'.malloc', '.memset', '.calloc'}
        if call0.intersection(mem_opt_funcs) and call1.intersection(mem_opt_funcs):
            return True
        return False

    # compare formulas and constraints 1 by 1
    already_matched_keys = set()
    for k0 in ks0:
        for k1 in ks1:
            if k1 in already_matched_keys:
                continue
            if not similar_libcalls(k0, k1):
                continue
            if k0[-1] in merged_args0.keys() and k1[-1] in merged_args1.keys():
                if merged_args0[k0[-1]][0][0] is None and merged_args1[k1[-1]][0][0] is None:
                    # here is a libcall with no argument
                    c0 = merged_args0[k0[-1]][0][2]
                    c1 = merged_args1[k1[-1]][0][2]
                    try:
                        if ast_prove_f1_equi_f2(c0, c1, 720):
                            for tmp_path in merged_args0[k0[-1]][0][1]:
                                already_matched_keys.add(tmp_path)
                            continue
                    except TooManyVariables4Comparison as e:
                        log.warning("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                                    (str(e.__class__), start0, filename0, start1, filename1))
                        # in this case, since we do not know whether they are equivalent.
                        # to achieve a low FN, we treat it as similar
                        for tmp_path in merged_args0[k0[-1]][0][1]:
                            already_matched_keys.add(tmp_path)
                        continue
                    except Exception as e:
                        log.error("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                                  (str(e), start0, filename0, start1, filename1))
                        for tmp_path in merged_args0[k0[-1]][0][1]:
                            already_matched_keys.add(tmp_path)
                        continue

            tmp = cmp(k0, k1)
            if tmp >= symbolic_eq_block_threshold:
                log.debug("%s matches %s" % (str(k0), str(k1)))
                already_matched_keys.add(k1)
                break
    return (start0, start1), (len(already_matched_keys) / len(ks0), 1.0 - sim)
    # queue.put(((start0, start1), (len(already_matched_keys) / len(ks0), 1.0 - sim)))


def compare_functions_with_queue(arg):
    res = compare_functions(arg)
    queue.put(res)


def compare_functions_with_pipe(conn):
    while True:
        arg = conn.recv()
        if isinstance(arg, str) and arg == 'end':
            conn.close()
            break
        res = compare_functions(arg)
        conn.send(res)


def compare_bins_with_multiprocess(d: Detector, processes):
    log.warning('start cross-comparing functions ...')
    assert queue.empty(), 'queue is not empty!!!'
    args, skipped = prepare_f_infos_list(d)
    # with multiprocessing.Pool(processes=processes) as p:
    #     p.map_async(func=compare_functions, iterable=args, chunksize=1)
    #     p.close()
    #     p.join()
    conns_main = []
    conns_subs = []
    for _ in range(processes):
        main_conn, sub_conn = multiprocessing.Pipe()
        conns_main.append(main_conn)
        conns_subs.append(sub_conn)
    ps = [multiprocessing.Process(target=compare_functions_with_pipe, args=(conns_subs[i],)) for i in range(processes)]
    for p in ps:
        p.start()
    idle_labels = [True for _ in range(processes)]
    for arg in args:
        # find an idle process and send arg
        for i in range(processes):
            if idle_labels[i]:
                conns_main[i].send(arg)
                idle_labels[i] = False
                break
        while True:
            has_idle = False
            for i in range(processes):
                if idle_labels[i]:
                    has_idle = True
                    break
                elif conns_main[i].poll():
                    tmp_res = conns_main[i].recv()
                    if tmp_res is not None:
                        queue.put(tmp_res)
                    idle_labels[i] = True
                    has_idle = True
                    break
            if has_idle:
                break
    # wait all result from sub processes
    for i in range(processes):
        if idle_labels[i]:
            conns_main[i].send('end')
        else:
            # conns_main[i].poll(timeout=None)
            tmp_res = conns_main[i].recv()
            if tmp_res is not None:
                queue.put(tmp_res)
            conns_main[i].send('end')
            idle_labels[i] = True
        conns_main[i].close()
        ps[i].join(timeout=1)
        ps[i].terminate()

    # for arg in args:
    #     compare_functions(arg)
    # after cross comparison
    similarity_matrix = dict()
    while not queue.empty():
        tmp = queue.get()
        f0_entry, f1_entry = tmp[0]
        if f0_entry not in similarity_matrix:
            similarity_matrix[f0_entry] = dict()
        similarity_matrix[f0_entry][f1_entry] = tmp[1]
        d._compared_res[(f0_entry, f1_entry)] = tmp[1]
    for (f0_entry, f1_entry) in skipped:
        if f0_entry not in similarity_matrix:
            similarity_matrix[f0_entry] = dict()
        similarity_matrix[f0_entry][f1_entry] = (0.0, _invalid_difference_value)
        d._compared_res[(f0_entry, f1_entry)] = (0.0, _invalid_difference_value)
    for f0_entry in similarity_matrix.keys():
        similarity_matrix[f0_entry] = Detector.sort_detect_similar_func_res(similarity_matrix[f0_entry])
    tmp = d._inline_cmp_functions_without_lib_calls()
    similarity_matrix.update(tmp)
    return similarity_matrix

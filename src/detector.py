import os, sys
import time
from enum import Enum
from queue import Queue
import pickle
import traceback
from src.cmp_claripy import prove_equal, ast_prove_f1_in_f2, ast_prove_f1_equi_f2
from src.cmp_tree import tree_equal, tree_distance
from src.error import *
from src.formulas_extractor import FormulaExtractor
from src.root_inst.root_inst_cfg import RootInstCFGBuilder, len_ri_path
from src.simple_cfg import *
from src.utils import *
from angr.sim_options import *
from src.similar_libcall import get_func_names_with_similar_libcall_replacement
from src.symbolic_exe_until_libcall import StopAtLibCallTech
import claripy
from src.root_inst.root_inst_cfg import _time_limit_for_a_func
from src.lib_call_args_analyze import get_libcall_args
import src
from tqdm import tqdm

_invalid_difference_value = 100000


def _random_select_n(a: list, n: int):
    """
    This function has side effect!
    """
    if len(a) > n:
        random.shuffle(a)
        a = a[:n]
    return a


def _save_pkl(obj, path):
    with open(path, 'wb') as f:
        pickle.dump(obj, f)


def _load_pkl(path):
    with open(path, 'rb') as f:
        return pickle.load(f)


class Detector:
    class Direction(Enum):
        CFG_PARENT = 0,
        PATH_PARENT = 1,
        MATCH = 2,  # left and up (45)
        NO_DIR = 3

    def __init__(self, p1: angr.Project, p2: angr.Project, mode='ted', alg='cop'):
        """
        The class for detecting the similarity of 2 binaries
        :param p1: The incoming program which needs to be tested (use linearly independent path of it)
        :param p2: The base program in our data base (use simple cfg of it)
        :param mode: The mode for comparing formulas and constraints, 'ted' and 'smt' are supported
        """
        self._p = [p1, p2]
        self._mode = mode

        self._eq_formulas_func = None
        if self._mode == 'ted':
            self._eq_formulas_func = tree_equal
        elif self._mode == 'smt':
            self._eq_formulas_func = prove_equal

        self._alg = alg
        assert self._eq_formulas_func is not None, 'wrong mode=%s' % self._mode

        # self._cfg = [self._p[0].analyses.CFGFast(), self._p[1].analyses.CFGFast()]
        self._cfg = [None, None]
        self._p_builder = [RootInstCFGBuilder(self._p[0], self._cfg[0]),
                           RootInstCFGBuilder(self._p[1], self._cfg[1])]

        self._state_options = ()
        self._no_constraints = False
        self._filter_assignment = True
        self._fe = [FormulaExtractor(self._p[0], self._cfg[0], mode=self._mode,
                                     state_options=self._state_options, no_constraints=self._no_constraints,
                                     filter_assignment=self._filter_assignment),
                    FormulaExtractor(self._p[1], self._cfg[1], mode=self._mode,
                                     state_options=self._state_options, no_constraints=self._no_constraints,
                                     filter_assignment=self._filter_assignment)]

        self.delta = dict()
        self.sigma = None

        # this result will be stored for avoiding redundant comparing
        # should be cleared after finishing comparison of 2 functions
        self._block_cmp_cache = dict()
        self._block_cmp_ted_cache = dict()

        self._symbolic_eq_block_threshold = 0.5
        self._refine_threshold = 0.8
        self._max_cmp_lip = int(1e2)
        # these collected lips are used to recover root-instruction-based simple cfg
        # I think this is not the bottle nack of our tools. 1e4 will take around 10s for collecting and recovering cfg.
        self._max_collected_lips = int(1e3)
        self._max_ci_depth = 10
        self._cfg_nodes_upper_bound = 1000

        # we need to store the LIPs and simple_cfg info of every function
        self._visited_CoP_funcs = [{}, {}]
        self._visited_RI_funcs = [{}, {}]
        self._visited_basic_block_scfgs = [{}, {}]
        self._visited_1st_libcall = [{}, {}]
        # record the callees dictionary, {func_entry: {instr_addr: (callee_entry, arguments instruction address list)}}
        self._visited_RI_callees = [{}, {}]
        self._current_callees = (None, None)
        # self._already_collected = [set(), set()]
        # store the results of compared pairs of functions. Keys are tuples of functions' keys
        self._compared_res = dict()

        # initializing while comparing
        self._valid_funcs = [self._get_valid_func_ida(0), self._get_valid_func_ida(1)]

        self.init_info_for_inline_mode()

    def get_x86_lib_call_arg_offsets(self, proj_id):
        return get_libcall_args(self._libcalls[proj_id], self._valid_funcs[proj_id], self._p[proj_id])

    def init_info_for_inline_mode(self):
        # must call following functions before
        if self._alg == 'inline':
            self._libcalls = [filter_libcall(self._get_func_addr_name_map(0)),
                              filter_libcall(self._get_func_addr_name_map(1))]
            try:
                self._call_matrix = [self.load_call_matrix(0), self.load_call_matrix(1)]
            except Exception:
                self.cache_all_basic_block_level_simple_cfg(0)
                self.cache_all_basic_block_level_simple_cfg(1)
                self._call_matrix = [self.get_call_graph_matrix(0), self.get_call_graph_matrix(1)]
            for proj_id in range(len(self._p)):
                if self._p[proj_id].arch.name == 'X86':
                    # for X86 software, we may need update the X86_CALL_ARGUMENTS_MAP first
                    # X86_CALL_ARGUMENTS_MAP.update(self.get_x86_lib_call_arg_offsets(proj_id))
                    tmp = self.get_x86_lib_call_arg_offsets(proj_id)
                    tmp.update(src.lib_call_arguments.X86_CALL_ARGUMENTS_MAP)
                    src.lib_call_arguments.X86_CALL_ARGUMENTS_MAP.update(tmp)

    def load_call_matrix(self, pid):
        prefix = self._p[pid].filename + '_analysis'
        save_to = os.path.join(prefix, 'call_matrix')
        return _load_pkl(save_to)

    def save_to_disk(self, p_ids=(0, 1)):
        """
        save analyzed data to disk, p0 and p1 respectively
        self._visited_RI_funcs
        self._visited_RI_callees
        self._fe
        """
        rec_limit = sys.getrecursionlimit()
        sys.setrecursionlimit(rec_limit * 5)
        for p_id in p_ids:
            prefix = self._p[p_id].filename + '_analysis'
            if not os.path.isdir(prefix):
                os.mkdir(prefix)
            with open(os.path.join(prefix, 'RI_funcs'), 'wb') as f:
                pickle.dump(self._visited_RI_funcs[p_id], f)
            with open(os.path.join(prefix, 'RI_callees'), 'wb') as f:
                pickle.dump(self._visited_RI_callees[p_id], f)
            with open(os.path.join(prefix, '1st_libcall'), 'wb') as f:
                pickle.dump(self._visited_1st_libcall[p_id], f)
            with open(os.path.join(prefix, 'call_matrix'), 'wb') as f:
                pickle.dump(self._call_matrix[p_id], f)
            self._fe[p_id].save_visit_data(os.path.join(prefix, 'fe_data'))
        sys.setrecursionlimit(rec_limit)

    def load_analysis(self, p_ids=(0, 1)):
        """
        :param p_ids:
        :return: return a tuple of failure projects' ids
        """
        load_fail = []
        for p_id in p_ids:
            prefix = self._p[p_id].filename + '_analysis'
            if not os.path.isdir(prefix):
                load_fail.append(p_id)
                continue
            try:
                with open(os.path.join(prefix, 'RI_funcs'), 'rb') as f:
                    self._visited_RI_funcs[p_id] = pickle.load(f)
                with open(os.path.join(prefix, 'RI_callees'), 'rb') as f:
                    self._visited_RI_callees[p_id] = pickle.load(f)
                with open(os.path.join(prefix, '1st_libcall'), 'rb') as f:
                    self._visited_1st_libcall[p_id] = pickle.load(f)
                # with open(os.path.join(prefix, 'call_matrix'), 'rb') as f:
                #     self._call_matrix[p_id] = pickle.load(f)
                self._fe[p_id].load_visit_data(os.path.join(prefix, 'fe_data'))
            except Exception:
                load_fail.append(p_id)
        return tuple(load_fail)

    def _eq_formulas(self, f1, f2, input1, input2):
        return self._eq_formulas_func(f1, f2, input1, input2)

    def get_paths_from(self, start, proj_id, inline_depth=0):
        """
        get CoP linearly independent path
        """
        if start in self._visited_CoP_funcs[proj_id]:
            if self._visited_CoP_funcs[proj_id][start][0] is not None:
                return self._visited_CoP_funcs[proj_id][start][0]
        start_time = time.time()
        log.warning('start building linearly independent path from address: 0x%x of program %s' %
                    (start, self._p[proj_id].filename))
        simple_cfg = self.get_simple_cfg_from(start, proj_id, inline_depth)
        # lips and simple_cfg should be cached
        self._visited_CoP_funcs[proj_id][start] = (simple_cfg.get_all_linearly_independent_paths(), simple_cfg)
        if inline_depth > 0:
            # TODO
            raise NotImplementedError('do not support function inline yet')
        log.info('finish building linearly independent path from address: 0x%x of program %s, time elapse: %f' %
                 (start, self._p[proj_id].filename, (time.time() - start_time)))
        return self._visited_CoP_funcs[proj_id][start][0]

    def get_simple_cfg_from(self, start, proj_id, inline_depth=0):
        if start in self._visited_CoP_funcs[proj_id]:
            return self._visited_CoP_funcs[proj_id][start][1]

        start_time = time.time()
        log.warning('start building simple CFG from address: 0x%x of program %s' %
                    (start, self._p[proj_id].filename))
        self._visited_CoP_funcs[proj_id][start] = (None, build_simple_cfg(start, self._cfg[proj_id]))
        if inline_depth > 0:
            # TODO
            raise NotImplementedError('not support function inline yet')
        log.info('finish building simple CFG from address: 0x%x of program %s, time elapse: %f' %
                 (start, self._p[proj_id].filename, (time.time() - start_time)))
        return self._visited_CoP_funcs[proj_id][start][1]

    def get_ri_lips_and_simple_cfg_from(self, start, proj_id, inline_depth=0):
        if start in self._visited_RI_funcs[proj_id]:
            if self._visited_RI_funcs[proj_id][start] is None:
                raise TooHardToSolveException(start, -1)
            return self._visited_RI_funcs[proj_id][start]
        start_time = time.time()
        log.warning('start building root instruction-based simple CFG from address: 0x%x of program %s' %
                    (start, self._p[proj_id].filename))
        if self._alg == 'cop':
            lips, scfg, num_callee, callees = self._p_builder[proj_id].build_func_ri_lips_and_cfg(
                start, self._max_collected_lips)
        elif self._alg == 'ci':
            lips, scfg, num_callee, callees = self._p_builder[proj_id].get_continuous_info_by_symbolic_execution(
                start, self._fe[proj_id], self._max_ci_depth)
        else:
            # cop is default alg
            lips, scfg, num_callee, callees = self._p_builder[proj_id].build_func_ri_lips_and_cfg(
                start, self._max_collected_lips)

        # store the callees info of this function, use this while collecting formulas
        self._visited_RI_callees[proj_id][start] = callees

        if len(scfg.pool) >= self._cfg_nodes_upper_bound:
            self._visited_RI_funcs[proj_id][start] = None
            raise TooHardToSolveException(start, len(scfg.pool))

        self._visited_RI_funcs[proj_id][start] = (lips, scfg, num_callee)
        if log.level <= 10:
            # default debug level, there may be thousands of lips
            log.debug('LIPs of function 0x%x :' % start)
            for lip in lips:
                log.debug(str(lip))

        log.info('finish building root instruction-based simple CFG from address: 0x%x of program %s, time elapse: %f' %
                 (start, self._p[proj_id].filename, (time.time() - start_time)))
        log.warning('func: 0x%x :  %d lips; %d cfg nodes; %d callees' % (start, len(lips), len(scfg.pool), num_callee))

        return self._visited_RI_funcs[proj_id][start]

    def get_formulas_and_constraints_from(self, block_id, proj_id):
        return self._fe[proj_id].get_formulas_from(block_id, self._current_callees[proj_id])

    def cmp_func(self, start0, start1, inline_depth0=0, inline_depth1=0, mode='ri', not_sym_exe=False, no_skip=False):
        """
        compare 2 functions in 1st and 2nd projects respectively
        :param start0: the block id in the 1st project
        :param start1: the block id in the 2nd project
        :param inline_depth0: control the depth of inline
        :param inline_depth1: control the depth of inline
        :return:
        """
        log.info('comparing functions 0x%x(%s) with 0x%x(%s)' %
                 (start0, self._p[0].filename, start1, self._p[1].filename))
        mode = mode.lower()
        if mode == 'ri' and self._alg == 'cop':
            if self.quick_cmp_func(start0, start1):
                return self._cmp_func_ri_mode(start0, start1, inline_depth0=0, inline_depth1=0)
            else:
                return 0.0, _invalid_difference_value
        elif mode == 'ri' and self._alg == 'ci':
            if self.quick_cmp_func(start0, start1):
                return self._cmp_func_ri_mode_continuously(start0, start1, inline_depth0=0, inline_depth1=0)
            else:
                return 0.0, _invalid_difference_value
            # return self._cmp_func_ri_mode(start0, start1, inline_depth0=0, inline_depth1=0)
        elif mode == 'cop':
            return self._cmp_func_cop_mode(start0, start1, inline_depth0=0, inline_depth1=0)
        elif self._alg == 'inline':
            # mode is useless here, self._mode must be smt
            assert self._mode == 'smt'
            sim = self._inlined_callees_cmp(start0, start1)
            if no_skip:
                return self._cmp_func_inline_mode(start0, start1, inline_depth0, inline_depth1, sim, not_sym_exe=not_sym_exe)
            else:
                if sim == -1:
                    # we do not handle this currently, but after finishing all functions with lib calls, the similarity
                    # of functions without lib calls can be calculated
                    return 0.0, _invalid_difference_value
                elif sim < 0.01:
                    # we do not run symbolic execution to compare these 2 functions
                    return 0.0, _invalid_difference_value
                else:
                    return self._cmp_func_inline_mode(start0, start1, inline_depth0, inline_depth1, sim, not_sym_exe=not_sym_exe)
        else:
            raise NotImplementedError()

    def quick_cmp_func(self, start0, start1):
        """
        We use the number of root instructions to check whether 2 functions should be possibly similar
        We merely implement it in root-instruction-based process
        :param start0:
        :param start1:
        :return: True if f1 and f2 may be similar, False if f1 and f2 cannot be similar
        """
        _, scfg0, num_call_0 = self.get_ri_lips_and_simple_cfg_from(start0, 0)
        _, scfg1, num_call_1 = self.get_ri_lips_and_simple_cfg_from(start1, 1)
        if num_call_0 > num_call_1:
            a = num_call_0
            b = num_call_1
        else:
            a = num_call_1
            b = num_call_0
        if b == 0 and a > 3:
            return False
        elif b > 0 and a / b > 2 and a - b > 3:
            return False
        return True
        # return abs(num_call_0 - num_call_1) < 5

    def _cmp_func_cop_mode(self, start0, start1, inline_depth0=0, inline_depth1=0):
        paths0 = self.get_paths_from(start0, 0, inline_depth0)
        simple_cfg1 = self.get_simple_cfg_from(start1, 1, inline_depth1)
        total_blocks_num = 0
        total_eq_blocks = 0
        for p in paths0:
            log.debug('original path: ' + str(p) + ' length: ' + str(len(p)))
            p = self.rm_invalid_blocks(p, 0)
            if len(p) == 0:
                # invalid path
                continue
            log.info('valid path: ' + str(p) + ' length: ' + str(len(p)))
            score, similarity = self.cmp_path_similarity(p, simple_cfg1)
            log.info('LCS: %d, ratio: %f' % (score, similarity))
            total_blocks_num += len(p)
            total_eq_blocks += score
        # finish comparison of 2 functions, these results should be seldom used
        self._block_cmp_cache.clear()

        if total_blocks_num == 0:
            raise InvalidFunctionException(start0)
        # TODO: 0 should be replaced by the difference of CFG of functions
        return total_eq_blocks / total_blocks_num, 0

    def _cmp_func_ri_mode(self, start0, start1, inline_depth0=0, inline_depth1=0):
        """
        If there is a function with no function call, we skip this pair temporarily
        :return:
        """
        lips0, simple_cfg0, _ = self.get_ri_lips_and_simple_cfg_from(start0, 0, inline_depth0)
        lips1, simple_cfg1, _ = self.get_ri_lips_and_simple_cfg_from(start1, 1, inline_depth1)
        self._set_current_callees(start0, start1)
        total_blocks_num = 0
        total_eq_blocks = 0

        lips0 = _random_select_n(lips0, self._max_cmp_lip)

        for p in lips0:
            log.debug('original path: ' + str(p) + ' length: ' + str(len_ri_path(p)))
            p = self.rm_invalid_blocks(p, 0, mode='both')
            if len(p) == 0:
                # invalid path
                continue
            log.info('valid path: ' + str(p) + ' length: ' + str(len_ri_path(p)))
            start_time = time.time()
            score, similarity = self.cmp_ri_path_similarity(p, simple_cfg1)
            log.info('LCS: %d, ratio: %f, elapse: %f' % (score, similarity, time.time() - start_time))
            total_blocks_num += len_ri_path(p)
            total_eq_blocks += score
        # finish comparison of 2 functions, these results should be seldom used
        self._block_cmp_cache.clear()
        self._reset_current_callees()

        if total_blocks_num == 0:
            raise InvalidFunctionException(start0)

        # in some conditions, f0 and f1 are different, but A is very small
        # so that it could match many other complex functions.
        # To solve this problem, we add the difference of number of nodes as an element to evaluate similarity
        return total_eq_blocks / total_blocks_num, abs(len(simple_cfg1.pool) - len(simple_cfg0.pool))

    def _cmp_func_ri_mode_continuously(self, start0, start1, inline_depth0=0, inline_depth1=0):
        lips0, simple_cfg0, num_callee0 = self.get_ri_lips_and_simple_cfg_from(start0, 0, inline_depth0)
        lips1, simple_cfg1, num_callee1 = self.get_ri_lips_and_simple_cfg_from(start1, 1, inline_depth1)
        if len(lips0) > 20 or len(lips1) > 20:
            # it seems too slow for our cases
            return 0.0, _invalid_difference_value
        self._set_current_callees(start0, start1)
        total_blocks_num = 0
        total_eq_blocks = 0
        for p in lips0:
            log.debug('original path: ' + str(p) + ' length: ' + str(len_ri_path(p)))
            start_time = time.time()
            is_valid, p_valid_start = self.is_a_valid_path(p, 0)
            if is_valid:
                score, similarity = self.cmp_ri_path_similarity_continuously(p, p_valid_start, simple_cfg1)
                log.info('LCS: %d, ratio: %f, elapse: %f' % (score, similarity, time.time() - start_time))
                total_blocks_num += len_ri_path(p)
                total_eq_blocks += score
        # finish comparison of 2 functions, these results should be seldom used
        self._block_cmp_cache.clear()
        self._reset_current_callees()

        if total_blocks_num == 0:
            raise InvalidFunctionException(start0)

        return total_eq_blocks / total_blocks_num, abs(len(simple_cfg1.pool) - len(simple_cfg0.pool))

    def get_formula_stop_at_lib_call(self, start, proj_id, not_sym_exe):
        if start not in self._visited_1st_libcall[proj_id]:
            if not_sym_exe:
                raise FunctionWithoutFormulaDataException(self._p[proj_id], start)
            log.info('collecting formulas from 0x%x(%s)' % (start, self._p[proj_id].filename))
            tech = StopAtLibCallTech(start, self._p[proj_id], self._fe[proj_id],
                                     self._libcalls[proj_id], self._valid_funcs[proj_id])
            simgr = self._p[proj_id].factory.simgr(tech.create_init_state(), techniques=[tech])
            try:
                with _time_limit_for_a_func(600, start):
                    simgr.run()
            except TimeoutForCollectingInfoException as e:
                log.error(str(e))
            except Exception as e:
                log.error('Unknown Exception %s 0x%x (%s)' % (str(e), start, self._p[proj_id].filename))
                exc_type, exc_obj, exc_tb = sys.exc_info()
                err_fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                log.error('Unexpected error from %s' % str((exc_type, err_fname, exc_tb.tb_lineno)))
                # log.error(traceback.format_exc())

            if len(tech.all_keys) > 0:
                # Should we collect info from return?
                tech.get_info_from_return_paths(simgr)
            # the precision improvement of merging formulas is no significant, but it cause relatively huge overhead
            # we do not use it currently
            if False:
                self._visited_1st_libcall[proj_id][start] = (tech.all_keys, None, None)
            else:
                self._visited_1st_libcall[proj_id][start] = (tech.all_keys, tech.all_lib_calls,
                                                             tech.merge_path_to_same_lib_call_together())

            # for key in self._visited_1st_libcall[proj_id][start]:
            #     print(self._fe[proj_id]._visited[key])

        return self._visited_1st_libcall[proj_id][start]

    def pop_collected_formulas(self, start, proj_id):
        """
        remove the data collected on this function
        """
        if start not in self._visited_1st_libcall[proj_id]:
            return
        ks, libcalls, merged_args = self._visited_1st_libcall[proj_id][start]
        for k in ks:
            self._fe[proj_id]._visited.pop(k)
        self._visited_1st_libcall[proj_id].pop(start)

    def _cmp_func_inline_mode(self, start0, start1, inline_depth0=0, inline_depth1=0, sim=0.0, not_sym_exe=False):
        """
        inline functions other than lib calls, collect the formulas of arguments of lib calls to compare the similarity
        of these 2 functions
        :param start0:
        :param start1:
        :param inline_depth0:
        :param inline_depth1:
        :return:
        """
        def merge_formula_with_constraints(block_id, proj_id):
            formulas, constraints, input = self.get_formulas_and_constraints_from(block_id, proj_id)
            log.debug('formulas    = %s (%s trace %s)' % (str(formulas), self._p[proj_id].filename, str(block_id)))
            log.debug('constraints = %s (%s trace %s)' % (str(constraints), self._p[proj_id].filename, str(block_id)))
            log.debug('read_from   = %s (%s trace %s)' % (str(input), self._p[proj_id].filename, str(block_id)))
            merged_formulas = []
            for f in formulas:
                # a tuple, (merged_formula, original_formula)
                # when the constraint on its path (or the path constraint of the block being compared) is already UNSAT
                # we use the original formula for comparison
                merged_formulas.append((merge_fe_formulas([(f[1], constraints)], ptr_size=f[1].size())[0], f[1]))
            log.debug(
                'merged_formulas = %s (%s trace %s)' % (str(merged_formulas), self._p[proj_id].filename, str(block_id)))
            return merged_formulas, constraints, input

        def cmp(block0, block1):
            # we merely support smt mode currently
            try:
                merged_f0, c0, in0 = merge_formula_with_constraints(block0, 0)
                merged_f1, c1, in1 = merge_formula_with_constraints(block1, 1)
                if len(merged_f0) > 0 and len(merged_f1) > 0:
                    already_matched = set()
                    for f0 in merged_f0:
                        for f1_idx in range(len(merged_f1)):
                            if f1_idx in already_matched:
                                continue
                            f1 = merged_f1[f1_idx]
                            if prove_equal(f0, f1, self._fe[0].ptr_size, self._fe[1].ptr_size, c0, c1, cmp_limit=120):
                                already_matched.add(f1_idx)
                                log.debug(f'Matched {str(f0)} and {str(f1)}')
                                break
                    if len(already_matched) > 0:
                        return len(already_matched) / len(merged_f0)
                    else:
                        # if no formula matches and the constraints are complex enough, we compare constraints only
                        if len(c0) + len(c1) > 2 \
                                and ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1),
                                                         self._fe[0].ptr_size, self._fe[1].ptr_size, cmp_limit=120):
                            return self._symbolic_eq_block_threshold
                        else:
                            return 0.0
                else:
                    # no formulas are collected, we compare constraints only
                    if ast_prove_f1_equi_f2(claripy.And(*c0), claripy.And(*c1), self._fe[0].ptr_size, self._fe[1].ptr_size, cmp_limit=720):
                        return self._symbolic_eq_block_threshold
            except TooManyVariables4Comparison as e:
                # the output of this error could be huge
                log.warning("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                            (str(e.__class__), start0, self._p[0].filename, start1, self._p[1].filename))
                # to achieve a low FN, we treat this case as positive
                return self._symbolic_eq_block_threshold
            except Exception as e:
                log.error("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                          (str(e), start0, self._p[0].filename, start1, self._p[1].filename))
                exc_type, exc_obj, exc_tb = sys.exc_info()
                err_fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                log.error('Unexpected error from %s' % str((exc_type, err_fname, exc_tb.tb_lineno)))
                # log.error(traceback.format_exc())
            return 0.0

        def endswith_libcall(path_trace, proj_id):
            if path_trace[-1] is None:
                return 'RETURN'
            if path_trace[-1] in self._libcalls[proj_id].keys():
                return self._libcalls[proj_id][path_trace[-1]]
            else:
                return None

        def similar_libcalls(trace0, trace1):
            call0, call1 = endswith_libcall(trace0, 0), endswith_libcall(trace1, 1)
            log.debug('traces end at libcall %s and %s' % (str(call0), str(call1)))
            # log.error('traces end at libcall %s and %s' % (str(call0), str(call1)))
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

        ks0, libcalls0, merged_args0 = self.get_formula_stop_at_lib_call(start0, 0, not_sym_exe)
        if len(ks0) == 0:
            log.warning('no lib call formulas are collected from 0x%x (%s)' % (start0, self._p[0].filename))
            raise InvalidFunctionException(start0)

        ks1, libcalls1, merged_args1 = self.get_formula_stop_at_lib_call(start1, 1, not_sym_exe)
        if len(ks1) == 0:
            log.warning('no lib call formulas are collected from 0x%x (%s)' % (start1, self._p[1].filename))
            raise InvalidFunctionException(start1)
        log.info('There are %d LIPs from %s and %d LIPs from %s' % (len(ks0), self._p[0].filename,
                                                                    len(ks1), self._p[1].filename))
        # compare merged formulas first
        # if libcalls0 is not None:
        #     # please have a look of helper function get_formula_keys
        #     already_matched_keys = set()
        #     all_merged_formulas_num = 0
        #     for libcall_addr0 in merged_args0.keys():
        #         for v0_name, merged_f0, valid_cons0 in merged_args0[libcall_addr0]:
        #             all_merged_formulas_num += 1
        #             for libcall_addr1 in merged_args1.keys():
        #                 tmp_matched = False
        #                 for v1_name, merged_f1, valid_cons1 in merged_args1[libcall_addr1]:
        #                     if (libcall_addr1, v1_name) in already_matched_keys:
        #                         continue
        #                     try:
        #                         if prove_equal(merged_f0, merged_f1, None, None, [valid_cons0], [valid_cons1],
        #                                        equal_var=False):
        #                             already_matched_keys.add((libcall_addr1, v1_name))
        #                             tmp_matched = True
        #                             break
        #                     except TooManyVariables4Comparison as e:
        #                         log.error(e.__class__)
        #                 if tmp_matched:
        #                     break
        #     if all_merged_formulas_num > 0 and len(already_matched_keys) / all_merged_formulas_num > 0:
        #         self._compared_res[(start0, start1)] = (len(already_matched_keys) / all_merged_formulas_num, 1.0 - sim)
        #         return self._compared_res[(start0, start1)]

        # compare formulas and constraints 1 by 1
        already_matched_keys = set()
        # compute the comparing times. if it is large than a threshold, we do not compare every 2 path, but use
        # the lib call as a filter
        comparing_count = len(ks0) * len(ks1)
        tried_merged_libcall = set()
        for k0 in ks0:
            for k1 in ks1:
                if k1 in already_matched_keys:
                    continue
                if (k0[-1], k1[-1]) in tried_merged_libcall:
                    continue
                if not similar_libcalls(k0, k1):
                    continue
                if k0[-1] in merged_args0.keys() and k1[-1] in merged_args1.keys():
                    if merged_args0[k0[-1]][0][0] is None and merged_args1[k1[-1]][0][0] is None:
                        # here is a libcall with no argument
                        tried_merged_libcall.add((k0[-1], k1[-1]))
                        c0 = merged_args0[k0[-1]][0][2]
                        c1 = merged_args1[k1[-1]][0][2]
                        try:
                            if ast_prove_f1_equi_f2(c0, c1, self._fe[0].ptr_size, self._fe[1].ptr_size, 720):
                                for tmp_path in merged_args0[k0[-1]][0][1]:
                                    already_matched_keys.add(tmp_path)
                                continue
                        except TooManyVariables4Comparison as e:
                            log.warning("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                                        (str(e.__class__), start0, self._p[0].filename, start1, self._p[1].filename))
                            # in this case, since we do not know whether they are equivalent.
                            # to achieve a low FN, we treat it as similar
                            for tmp_path in merged_args0[k0[-1]][0][1]:
                                already_matched_keys.add(tmp_path)
                            continue
                        except Exception as e:
                            log.error("meet %s while comparing 0x%x (%s) with 0x%x (%s)" %
                                      (str(e), start0, self._p[0].filename, start1, self._p[1].filename))
                            exc_type, exc_obj, exc_tb = sys.exc_info()
                            err_fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                            log.error('Unexpected error from %s' % str((exc_type, err_fname, exc_tb.tb_lineno)))
                            # log.error(traceback.format_exc())
                            for tmp_path in merged_args0[k0[-1]][0][1]:
                                already_matched_keys.add(tmp_path)
                            continue

                tmp = cmp(k0, k1)
                if tmp >= self._symbolic_eq_block_threshold:
                    already_matched_keys.add(k1)
                    break
        self._compared_res[(start0, start1)] = (len(already_matched_keys) / len(ks0), 1.0 - sim)
        return self._compared_res[(start0, start1)]

    def cmp_blocks(self, block0, block1, _constraint2formula_ratio=1):
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
        matched = 0
        already_matched = set()
        for f0 in formulas0:
            for f1_idx in range(len(formulas1)):
                if f1_idx in already_matched:
                    continue
                if self._eq_formulas(f0[1], formulas1[f1_idx][1], input0, input1):
                    matched += 1
                    already_matched.add(f1_idx)
                    break
        already_matched.clear()
        for c0 in constraints0:
            for c1_idx in range(len(constraints1)):
                if c1_idx in already_matched:
                    continue
                if self._eq_formulas(c0, constraints1[c1_idx], input0, input1):
                    matched += _constraint2formula_ratio
                    already_matched.add(c1_idx)
                    break
        if len(formulas0) + _constraint2formula_ratio * len(constraints0) == 0:
            return 0.0
        return matched / (len(formulas0) + _constraint2formula_ratio * len(constraints0))

    def cmp_first_formula_only(self, block0, block1):
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        if len(formulas0) == 0:
            return 0.0
        formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
        if len(formulas1) == 0:
            return 0.0
        if self._eq_formulas(formulas0[0][1], formulas1[0][1], input0, input1):
            return 1.0
        return 0.0

    def get_minimum_tree_edit_distance(self, block0, block1):
        if (block0, block1) not in self._block_cmp_ted_cache.keys():
            if self._no_constraints:
                formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
                if len(formulas0) == 0:
                    return 0, -1
                formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
                if len(formulas1) == 0:
                    return 0, -1
                already_matched = set()
                total_ted = 0
                for f0 in formulas0:
                    min_d_of_f0 = 1000000
                    if len(already_matched) == len(formulas1):
                        # no formulas in block1 for comparing
                        min_d_of_f0 = len(f0[1].children) + 1
                    else:
                        for f1_idx in range(len(formulas1)):
                            if f1_idx in already_matched:
                                continue
                            min_d_of_f0 = min(tree_distance(f0[1], formulas1[f1_idx][1], input0, input1), min_d_of_f0)
                            if min_d_of_f0 == 0:
                                already_matched.add(f1_idx)
                                break
                    total_ted += min_d_of_f0
                return total_ted, len(formulas0)
            else:
                formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
                if len(formulas0) + len(constraints0) == 0:
                    return 0, -1
                formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
                if len(formulas1) + len(constraints1) == 0:
                    return 0, -1
                already_matched = set()
                total_ted = 0
                for f0 in formulas0:
                    min_d_of_f0 = 1000000
                    if len(already_matched) == len(formulas1):
                        # no formulas in block1 for comparing
                        min_d_of_f0 = len(f0[1].children) + 1
                    else:
                        for f1_idx in range(len(formulas1)):
                            if f1_idx in already_matched:
                                continue
                            min_d_of_f0 = min(tree_distance(f0[1], formulas1[f1_idx][1], input0, input1), min_d_of_f0)
                            if min_d_of_f0 == 0:
                                already_matched.add(f1_idx)
                                break
                    total_ted += min_d_of_f0

                already_matched.clear()
                for c0 in constraints0:
                    min_d_of_c0 = 1000000
                    if len(already_matched) == len(constraints1):
                        # no formulas in block1 for comparing
                        min_d_of_c0 = len(c0.children) + 1
                    else:
                        for c1_idx in range(len(constraints1)):
                            if c1_idx in already_matched:
                                continue
                            min_d_of_c0 = min(tree_distance(c0, constraints1[c1_idx], input0, input1), min_d_of_c0)
                            if min_d_of_c0 == 0:
                                already_matched.add(c1_idx)
                                break
                    total_ted += min_d_of_c0
                return total_ted, len(formulas0) + len(constraints0)

    def cmp_blocks_formulas(self, block0, block1):
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        if len(formulas0) == 0:
            return 0.0
        formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
        matched = 0
        already_matched = set()
        for f0 in formulas0:
            for f1_idx in range(len(formulas1)):
                if f1_idx in already_matched:
                    continue
                if self._eq_formulas(f0[1], formulas1[f1_idx][1], input0, input1):
                    matched += 1
                    already_matched.add(f1_idx)
                    break
        return matched / len(formulas0)

    def cmp_blocks_constraints(self, block0, block1):
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        formulas1, constraints1, input1 = self.get_formulas_and_constraints_from(block1, 1)
        matched = 0
        already_matched = set()
        for c0 in constraints0:
            for c1_idx in range(len(constraints1)):
                if c1_idx in already_matched:
                    continue
                if self._eq_formulas(c0, constraints1[c1_idx], input0, input1):
                    matched += 1
                    already_matched.add(c1_idx)
                    break
        return matched / len(constraints0)

    def valid_block(self, block_id, proj_id, mode='formulas'):
        formulas, constraints, _ = self.get_formulas_and_constraints_from(block_id, proj_id)
        if mode == 'formulas':
            return len(formulas) > 0
        elif mode == 'constraints':
            return len(constraints) > 0
        else:
            return (len(formulas) + len(constraints)) > 0

    def rm_invalid_blocks(self, path: list, proj_id, mode='formulas'):
        filtered_path = []
        for block_id in path:
            if self.valid_block(block_id, proj_id, mode):
                # for a block with no formulas, such as only a `ret`, we just remove it
                filtered_path.append(block_id)
        return filtered_path

    def print_a_block(self, block_id, proj_id):
        formulas, constraints, symbol_inputs = self.get_formulas_and_constraints_from(block_id, proj_id)
        print('block id: %d (%d)' % (block_id, proj_id))
        for f in formulas:
            print('%s = %s' % (f[0], str(f[1])))
        print('constraints')
        for c in constraints:
            print(str(c))

    def _set_current_callees(self, start0, start1):
        self._current_callees = (self._visited_RI_callees[0][start0], self._visited_RI_callees[1][start1])

    def _reset_current_callees(self):
        self._current_callees = (None, None)

    def is_symbolic_eq_blocks(self, block0, block1):
        if (block0, block1) not in self._block_cmp_cache.keys():
            # TODO: cmp_blocks_formulas may be changed (a hybrid of formulas and constraints?)
            if self._no_constraints:
                self._block_cmp_cache[(block0, block1)] = self.cmp_blocks_formulas(block0, block1)
            else:
                self._block_cmp_cache[(block0, block1)] = self.cmp_blocks(block0, block1)
            # self._block_cmp_cache[(block0, block1)] = self.cmp_first_formula_only(block0, block1)
        return self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold
        # if (block0, block1) not in self._block_cmp_ted_cache:
        #     self._block_cmp_ted_cache[(block0, block1)] = self.get_minimum_tree_edit_distance(block0, block1)
        #     log.debug('compare %s vs. %s : %s' % (block0, block1, str(self._block_cmp_ted_cache[(block0, block1)])))
        # return self._block_cmp_ted_cache[(block0, block1)][0] < self._block_cmp_ted_cache[(block0, block1)][1] // 2

    def cmp_path_similarity(self, path0, simple_cfg1: SimpleCFG):
        # build a table to calculate the LCS, though I use a dictionary here
        delta = {0: [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]}
        # for block_id, node in simple_cfg1.pool.items():
        #     delta[block_id] = [(0, self.Direction.NO_DIR) for _ in range(n+1)]
        q = Queue()
        q.put(simple_cfg1.root)
        while not q.empty():
            cur_node_id = q.get_nowait()
            for mu in simple_cfg1.get_node(cur_node_id).children:
                self.LCS(path0, mu, cur_node_id, delta, q)
        highest_score = 0
        last_block_id = None
        for block_id, _l in delta.items():
            if _l[-1][0] > highest_score:
                highest_score = _l[-1][0]
                last_block_id = block_id

        # propagate back to recover the corresponding LCS in CFG
        if last_block_id:
            lcs_res = self._recover_LCS_in_CFG(last_block_id, path0, delta)
            log.debug(str(lcs_res))
        else:
            log.debug('No LCS')

        # TODO: if the highest_score > threshold, then do refineLCS

        return highest_score, highest_score / len(path0)

    def cmp_ri_path_similarity(self, path0, simple_cfg1: SimpleCFG, verbose=0):
        # build a table to calculate the LCS, though I use a dictionary here
        delta = {0: [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]}
        # for block_id, node in simple_cfg1.pool.items():
        #     delta[block_id] = [(0, self.Direction.NO_DIR) for _ in range(n+1)]
        q = Queue()
        q.put(simple_cfg1.root)
        while not q.empty():
            cur_node_id = q.get_nowait()
            for mu in simple_cfg1.get_node(cur_node_id).children:
                self.ri_LCS(path0, mu, cur_node_id, delta, q)
        highest_score = 0
        last_block_id = None
        for block_id, _l in delta.items():
            if _l[-1][0] > highest_score:
                highest_score = _l[-1][0]
                last_block_id = block_id

        # propagate back to recover the corresponding LCS in CFG
        if verbose > 0:
            if last_block_id:
                lcs_res = self._recover_LCS_in_CFG(last_block_id, path0, delta)
                log.debug(str(lcs_res))
            else:
                log.debug('No LCS')

        # compute the length of path0
        return highest_score, highest_score / len_ri_path(path0)

    def is_a_valid_path(self, path, proj_id):
        path_valid_start = 0
        while path_valid_start < len(path) and \
                not self.valid_block(path[:path_valid_start + 1], proj_id, mode='both'):
            path_valid_start += 1
        return path_valid_start < len(path), path_valid_start

    def cmp_ri_path_similarity_continuously(self, path0, path0_valid_start, simple_cfg1: SimpleCFG, verbose=1):
        # build a table to calculate the LCS, though I use a dictionary here
        delta = {0: [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]}

        q = Queue()
        q.put(simple_cfg1.root)
        while not q.empty():
            cur_node_id = q.get_nowait()
            for mu in simple_cfg1.get_node(cur_node_id).children:
                self.ri_LCS_continuously(path0, path0_valid_start, mu, cur_node_id, delta, q)
        highest_score = 0
        last_block_id = None
        for block_id, _l in delta.items():
            if _l[-1][0] > highest_score:
                highest_score = _l[-1][0]
                last_block_id = block_id

        # propagate back to recover the corresponding LCS in CFG
        if verbose > 0:
            if last_block_id:
                lcs_res = self._recover_LCS_in_CFG(last_block_id, path0, delta)
                log.debug(str(lcs_res))
            else:
                log.debug('No LCS')

        # compute the length of path0
        return highest_score, highest_score / len_ri_path(path0)

    def LCS(self, path0: list, mu, mu_parent, delta: dict, q: Queue):
        enqueue = False
        if mu not in delta.keys():
            # it is the 1st visit of this block, enqueue it anyway
            enqueue = True
            delta[mu] = [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]
        for p0_idx in range(len(path0)):
            if self.is_symbolic_eq_blocks(path0[p0_idx], mu):
                # here is a pair of matched blocks, compute the LCS from [0] of path0 to ([p0_idx], mu)
                # note that the index of p0_idx points to the block of p0_idx-1
                tmp_lcs = delta[mu_parent][p0_idx][0] + 1
                if tmp_lcs > delta[mu][p0_idx + 1][0]:
                    delta[mu][p0_idx + 1] = (tmp_lcs, self.Direction.MATCH, mu_parent)
                    # we know that the LCS to this block has updated, mu needs to be enqueued
                    enqueue = True
            else:
                # update the value according to its own, parent's and brother's value. Select the largest one.
                if delta[mu_parent][p0_idx + 1][0] > delta[mu][p0_idx][0]:
                    if delta[mu][p0_idx + 1][0] < delta[mu_parent][p0_idx + 1][0]:
                        # copy the LCS from its parent
                        delta[mu][p0_idx + 1] = (delta[mu_parent][p0_idx + 1][0], self.Direction.CFG_PARENT, mu_parent)
                        enqueue = True
                else:
                    if delta[mu][p0_idx + 1][0] < delta[mu][p0_idx][0]:
                        # success the LCS from the former target block
                        # this iteration compute the LCS of path (0, 1, ..., v_idx), since v_idx does not match mu
                        # we get LCS of (v_idx, mu) from (v_idx-1, mu)
                        delta[mu][p0_idx + 1] = (delta[mu][p0_idx][0], self.Direction.PATH_PARENT)
                        enqueue = True
        if enqueue:
            q.put(mu)

    def ri_LCS(self, path0: list, mu, mu_parent, delta: dict, q: Queue):
        enqueue = False
        if mu not in delta.keys():
            # it is the 1st visit of this block, enqueue it anyway
            enqueue = True
            delta[mu] = [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]
        for p0_idx in range(len(path0)):
            if self.is_symbolic_eq_blocks(path0[p0_idx], mu):
                # we add more score if this ri-block contains more basic blocks
                tmp_lcs = delta[mu_parent][p0_idx][0] + len(path0[p0_idx])
                if tmp_lcs > delta[mu][p0_idx + 1][0]:
                    delta[mu][p0_idx + 1] = (tmp_lcs, self.Direction.MATCH, mu_parent)
                    # we know that the LCS to this block has updated, mu needs to be enqueued
                    enqueue = True
            else:
                # update the value according to its own, parent's and brother's value. Select the largest one.
                if delta[mu_parent][p0_idx + 1][0] > delta[mu][p0_idx][0]:
                    if delta[mu][p0_idx + 1][0] < delta[mu_parent][p0_idx + 1][0]:
                        # copy the LCS from its parent
                        delta[mu][p0_idx + 1] = (delta[mu_parent][p0_idx + 1][0], self.Direction.CFG_PARENT, mu_parent)
                        enqueue = True
                else:
                    if delta[mu][p0_idx + 1][0] < delta[mu][p0_idx][0]:
                        # success the LCS from the former target block
                        # this iteration compute the LCS of path (0, 1, ..., v_idx), since v_idx does not match mu
                        # we get LCS of (v_idx, mu) from (v_idx-1, mu)
                        delta[mu][p0_idx + 1] = (delta[mu][p0_idx][0], self.Direction.PATH_PARENT)
                        enqueue = True
        if enqueue:
            q.put(mu)

    def is_symbolic_eq_blocks_continuously(self, block0, block1):
        if (block0, block1) in self._block_cmp_cache.keys():
            return self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold

        self._block_cmp_cache[(block0, block1)] = 0.0
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        divisor = len(formulas0) + len(constraints0)
        if divisor == 0:
            # this block has no constraints and no formulas
            log.debug("%s of %s has no formula and constraint" % (str(block0), self._p[0].filename))
            self._block_cmp_cache[(block0, block1)] = 0.0
            return self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold

        info1 = self._fe[1]._visited_ci[block1]

        if len(formulas0) > 0:
            b1_fc_list = []
            b1_inputs = set()
            for formulas1, constraints1, input1 in info1:
                # we merely collected formula of rdi
                if formulas1:
                    b1_fc_list.append((formulas1[0][1], constraints1))
                    b1_inputs.update(input1)
            f1, b1_constraints = merge_fe_formulas(b1_fc_list, 64)
            if f1 is None:
                return False
            if ast_prove_f1_in_f2(formulas0[0][1], f1, [claripy.And(*constraints0)], b1_constraints):
                self._block_cmp_cache[(block0, block1)] = 1.0
        else:
            # no formulas of block0, compare every constraints
            for formulas1, constraints1, input1 in info1:
                if ast_prove_f1_equi_f2(claripy.And(*constraints0), claripy.And(*constraints1)):
                    self._block_cmp_cache[(block0, block1)] = 1.0
                    break
        return self._block_cmp_cache[(block0, block1)]

    def is_symbolic_eq_blocks_continuously2(self, block0, block1):
        self._block_cmp_cache[(block0, block1)] = 0.0
        formulas0, constraints0, input0 = self.get_formulas_and_constraints_from(block0, 0)
        divisor = len(formulas0) + len(constraints0)
        if divisor == 0:
            log.debug("%s of %s has no formula and constraint" % (str(block0), self._p[0].filename))
            self._block_cmp_cache[(block0, block1)] = 0.0
            return self._block_cmp_cache[(block0, block1)]
        prior_regs = ['rdi', 'rsi']
        info1 = self._fe[1]._visited_ci[block1]

        # test the special registers first
        for formulas1, constraints1, input1 in info1:
            for reg in prior_regs:
                for f0 in formulas0:
                    if reg == f0[0]:
                        for f1 in formulas1:
                            if reg == f1[0]:
                                if prove_equal(f0[1], f1[1], self._fe[0].ptr_size, self._fe[1].ptr_size, constraints0, constraints1):
                                    self._block_cmp_cache[(block0, block1)] = 1.0
        if self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold:
            return True

        # test all registers
        for formulas1, constraints1, input1 in info1:
            matched = 0
            constraint_matched = prove_equal(claripy.And(*constraints0), claripy.And(*constraints1), self._fe[0].ptr_size, self._fe[1].ptr_size)
            already_matched = set()
            for f0 in formulas0:
                for f1 in formulas1:
                    if f1[0] in already_matched:
                        continue
                    if constraint_matched:
                        if prove_equal(f0[1], f1[1], self._fe[0].ptr_size, self._fe[1].ptr_size):
                            matched += 1
                            already_matched.add(f1[0])
                    else:
                        if prove_equal(f0[1], f1[1], self._fe[0].ptr_size, self._fe[1].ptr_size, constraints0, constraints1):
                            matched += 1
                            already_matched.add(f1[0])
            if constraint_matched:
                self._block_cmp_cache[(block0, block1)] = max((matched + len(constraints0)) / divisor,
                                                              self._block_cmp_cache[(block0, block1)])
            elif divisor > len(constraints0):
                self._block_cmp_cache[(block0, block1)] = max(matched / (divisor - len(constraints0)),
                                                              self._block_cmp_cache[(block0, block1)])
            if self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold:
                return True
        return self._block_cmp_cache[(block0, block1)] >= self._symbolic_eq_block_threshold

    def ri_LCS_continuously(self, path0: tuple, valid_start, mu, mu_parent, delta: dict, q: Queue):
        enqueue = False
        if mu not in delta.keys():
            # it is the 1st visit of this block, enqueue it anyway
            enqueue = True
            delta[mu] = [(0, self.Direction.NO_DIR) for _ in range(len(path0) + 1)]
        for p0_idx in range(valid_start, len(path0)):
            if self.is_symbolic_eq_blocks_continuously(path0[:p0_idx + 1], mu):
                # we add more score if this ri-block contains more basic blocks
                tmp_lcs = delta[mu_parent][p0_idx][0] + len(path0[p0_idx])
                if tmp_lcs > delta[mu][p0_idx + 1][0]:
                    delta[mu][p0_idx + 1] = (tmp_lcs, self.Direction.MATCH, mu_parent)
                    # we know that the LCS to this block has updated, mu needs to be enqueued
                    enqueue = True
            else:
                # update the value according to its own, parent's and brother's value. Select the largest one.
                if delta[mu_parent][p0_idx + 1][0] > delta[mu][p0_idx][0]:
                    if delta[mu][p0_idx + 1][0] < delta[mu_parent][p0_idx + 1][0]:
                        # copy the LCS from its parent
                        delta[mu][p0_idx + 1] = (delta[mu_parent][p0_idx + 1][0], self.Direction.CFG_PARENT, mu_parent)
                        enqueue = True
                else:
                    if delta[mu][p0_idx + 1][0] < delta[mu][p0_idx][0]:
                        # success the LCS from the former target block
                        # this iteration compute the LCS of path (0, 1, ..., v_idx), since v_idx does not match mu
                        # we get LCS of (v_idx, mu) from (v_idx-1, mu)
                        delta[mu][p0_idx + 1] = (delta[mu][p0_idx][0], self.Direction.PATH_PARENT)
                        enqueue = True
        if enqueue:
            q.put(mu)

    def _recover_LCS_in_CFG(self, last_block, path0: list, delta: dict):
        # if a pair is Direction.CFG_PARENT, then this block in simple_cfg1 is not matched
        # if a pair is Direction.PATH_PARENT, then this block in path0 is not matched
        res = []
        cur_path0_idx = len(path0)  # note it is the (path0_idx + 1)
        cur_block = last_block
        while cur_path0_idx > 0:
            if delta[cur_block][cur_path0_idx][1] is self.Direction.MATCH:
                tmp_len, _, parent = delta[cur_block][cur_path0_idx]
                cur_path0_idx -= 1
                res.append((cur_block, 'MATCH', path0[cur_path0_idx], tmp_len))
                cur_block = parent
            elif delta[cur_block][cur_path0_idx][1] is self.Direction.CFG_PARENT:
                tmp_len, _, parent = delta[cur_block][cur_path0_idx]
                res.append((cur_block, 'NO-MATCH', tmp_len))
                cur_block = parent
            elif delta[cur_block][cur_path0_idx][1] is self.Direction.PATH_PARENT:
                tmp_len, _ = delta[cur_block][cur_path0_idx]
                cur_path0_idx -= 1
                res.append(('SKIP', path0[cur_path0_idx]))
            else:
                break
        res.reverse()
        return res

    def _get_valid_func_angr(self, proj_id):
        """
        get the set of keys of all valid functions
        we skip functions of plt, simprocedure, and syscall
        we merely check functions being located in .text section
        """
        valid_funcs = set()
        text_range = get_section_range(self._p[proj_id], '.text')
        for f_k, f in self._cfg[proj_id].functions.items():
            if f.addr in text_range:
                if not (f.is_plt or f.is_simprocedure or f.is_syscall):
                    assert f_k == f.addr, "f_key != f.addr"
                    valid_funcs.add(f.addr)
        return valid_funcs

    def _get_valid_func_ida(self, proj_id):
        """
        get the set of keys of all valid functions
        we skip functions of plt, simprocedure, and syscall
        we merely check functions being located in .text section
        """
        return self._p_builder[proj_id].get_all_functions()

    def cache_all_basic_block_level_simple_cfg(self, proj_id):
        """
        We must get all valid functions before calling this
        :param proj_id:
        :return:
        """
        func_n = len(self._valid_funcs[proj_id])
        count = 0
        step = 100
        pbar = tqdm(func_n)
        for func_entry in self._valid_funcs[proj_id]:
            count += 1
            # the returns are scfg, callees, num_callee
            self._visited_basic_block_scfgs[proj_id][func_entry] = \
                self._p_builder[proj_id].build_func_basic_block_level_simple_cfg(func_entry)
            if count % step == 0:
                pbar.update(step)
        pbar.close()

    def get_call_graph_matrix(self, proj_id):
        """
        must call cache_all_basic_block_level_simple_cfg before calling this
        """
        matrix = dict()
        all_text_sec_func_entries = self._visited_basic_block_scfgs[proj_id].keys()
        # initialize direct call first
        for caller_entry, info in self._visited_basic_block_scfgs[proj_id].items():
            _, callees, _ = info
            matrix[caller_entry] = [dict(), set()]  # [functions-in-text-section, lib-calls]
            for inst_addr, callee_info in callees.items():
                callee_entry, _ = callee_info
                if callee_entry in all_text_sec_func_entries:
                    matrix[caller_entry][0][callee_entry] = 1
                else:
                    matrix[caller_entry][1].add(callee_entry)

        # apart from above approach to initialize the matrix, we also do a deeper analysis on the data of IDA pro,
        # which provides all references to a function (we treat this as a caller of this function)
        refs_data_dir = self._p[proj_id].filename + '_functions_refs'
        offset = get_offset(self._p[proj_id])
        for callee_entry, info in self._visited_basic_block_scfgs[proj_id].items():
            caller_file = os.path.join(refs_data_dir, '0x%x.json' % (callee_entry - offset))
            with open(caller_file, 'r') as cf:
                callers = json.load(cf)
                # the callers should be a list
                assert isinstance(callers, list)
                for caller in callers:
                    if (caller + offset) not in all_text_sec_func_entries:
                        continue
                    if callee_entry in all_text_sec_func_entries:
                        matrix[caller + offset][0][callee_entry] = 1
                    else:
                        matrix[caller + offset][1].add(callee_entry)

        # update the matrix repeatedly, until no modification on the matrix
        max_loop_count = len(matrix)
        for loop_count in range(max_loop_count):
            updated = False
            for caller_entry in matrix.keys():
                user_def_callee_num = len(matrix[caller_entry][0])
                extn_def_callee_num = len(matrix[caller_entry][1])
                update_user_call = matrix[caller_entry][0].copy()
                update_extn_call = matrix[caller_entry][1].copy()
                for callee_entry, depth in matrix[caller_entry][0].items():
                    for next_callee_entry, next_depth in matrix[callee_entry][0].items():
                        if next_callee_entry not in update_user_call:
                            update_user_call[next_callee_entry] = next_depth + depth
                        update_extn_call.update(matrix[next_callee_entry][1])
                    update_extn_call.update(matrix[callee_entry][1])
                if len(update_user_call) != user_def_callee_num or len(update_extn_call) != extn_def_callee_num:
                    updated = True
                    matrix[caller_entry][0] = update_user_call
                    matrix[caller_entry][1] = update_extn_call
            if not updated:
                break
        return matrix

    def get_all_functions_without_lib_calls(self, proj_id):
        res = []
        for entry, info in self._call_matrix[proj_id].items():
            if len(info[1]) == 0:
                res.append(entry)
        return res

    def get_all_callers_of_func(self, func_entry, proj_id):
        res = []
        for entry, info in self._call_matrix[proj_id].items():
            if func_entry in info[0].keys():
                # caller_entry, depth
                res.append((entry, info[0][func_entry]))
        return res

    def cmp_caller_similarity(self, start0, start1, gamma=0.9):
        callers0 = self.get_all_callers_of_func(start0, 0)
        if len(callers0) == 0:
            # no caller of this function
            log.warning('No caller of function 0x%x, cannot calculate the similarity based on call graph' % start0)
            raise InvalidFunctionException(start0)
        callers1 = self.get_all_callers_of_func(start1, 0)
        # get the max similarity of every caller0
        max_sim_res = dict()
        for caller0, _ in callers0:
            max_sim_res[caller0] = (0.0, _invalid_difference_value)
            for caller1, _ in callers1:
                tmp_key = (caller0, caller1)
                if tmp_key in self._compared_res:
                    if self._compared_res[tmp_key][0] > max_sim_res[caller0][0]:
                        max_sim_res[caller0] = self._compared_res[tmp_key]
                    elif self._compared_res[tmp_key][0] == max_sim_res[caller0][0] \
                            and self._compared_res[tmp_key][1] < max_sim_res[caller0][1]:
                        max_sim_res[caller0] = self._compared_res[tmp_key]
        # the average of all max similarity is the finial similarity
        # the difference is the difference of number of callers
        avg_sim = 0.0
        for caller0, depth in callers0:
            avg_sim += max_sim_res[caller0][0] * (gamma ** (depth - 1))
        avg_sim = avg_sim / len(callers0)
        difference = abs(len(callers0) - len(callers1))
        return avg_sim, difference

    def get_inline_callees_of_a_func(self, func_entry, proj_id):
        """
        We must get all scfg, callees of every function before calling this
        The callees of callees of this function (foo) is also regarded as callees of foo
        We merely return the set of all callees' entries, the number of arguments each call is not included
        :param func_entry:
        :param proj_id:
        :return:
        """
        return set(self._call_matrix[proj_id][func_entry][0].keys()), self._call_matrix[proj_id][func_entry][1]

    def get_inline_callees_of_a_func2(self, func_entry, proj_id):
        scfg, callees, num_callees = self._visited_basic_block_scfgs[proj_id][func_entry]
        res_text_sec = set()
        res_other_sec = set()
        stack = []

        def push_callees(_callees: dict):
            for call_instr_addr, info in _callees.items():
                tmp_callee_entry, tmp_args = info
                stack.append(tmp_callee_entry)

        push_callees(callees)
        while len(stack) > 0:
            callee_entry = stack.pop()
            if callee_entry in res_text_sec or callee_entry in res_other_sec:
                continue
            if callee_entry in self._visited_basic_block_scfgs[proj_id].keys():
                res_text_sec.add(callee_entry)
                _, callees, _ = self._visited_basic_block_scfgs[proj_id][callee_entry]
                push_callees(callees)
            else:
                # this means the callee is not a part of text section, save it in another set
                res_other_sec.add(callee_entry)
        # With a naive classification, the functions not in text are likely be import functions or export functions
        # the symbols of functions in res_other_sec are likely to not be stripped
        return res_text_sec, res_other_sec

    def get_names_of_funcs(self, funcs, proj_id):
        fmap = self._get_func_addr_name_map(proj_id)
        res = list()
        for f_addr in funcs:
            res.append(fmap[f_addr])
        return res

    def _inlined_callees_cmp(self, start0, start1):
        text_sec_callees0, other_sec_callees0 = self.get_inline_callees_of_a_func(start0, 0)
        text_sec_callees1, other_sec_callees1 = self.get_inline_callees_of_a_func(start1, 1)
        if len(other_sec_callees0) == 0 and len(other_sec_callees1) == 0:
            # no lib call, we need to compare it with other functions in other way
            log.debug('both do not invoke functions in other sections')
            return -1
        # the function names in text section cannot be used, since they do not exist after strip
        # lib calls can be used to show the basic functionality of functions
        callee_names0 = self.get_names_of_funcs(other_sec_callees0, 0)
        callee_names1 = self.get_names_of_funcs(other_sec_callees1, 1)
        log.debug(str(callee_names0))
        log.debug(str(callee_names1))
        log.debug(str(self.get_names_of_funcs(text_sec_callees0, 0)))
        log.debug(str(self.get_names_of_funcs(text_sec_callees1, 1)))
        # normalize libcall names
        # callee_names0 = set(map(lambda n: n if n.startswith('.') else f'.{n}', callee_names0))
        # callee_names1 = set(map(lambda n: n if n.startswith('.') else f'.{n}', callee_names1))
        # measure the similarity of lib calls
        # By obfuscation, it is possible to introduce useless functions
        # Some functions are special. Their functionalities are the same, but are different due to compilation options
        # Such as _printf and ___printf_chk
        tmp_callee_names0 = set(get_func_names_with_similar_libcall_replacement(callee_names0))
        tmp_callee_names1 = set(get_func_names_with_similar_libcall_replacement(callee_names1))
        log.debug(str(tmp_callee_names0))
        log.debug(str(tmp_callee_names1))
        if len(tmp_callee_names0) == 0 or len(tmp_callee_names1) == 0:
            if len(tmp_callee_names0) == len(tmp_callee_names1):
                # both are 0, which means all relative lib calls are likely being inlined
                # how to solve this situation has not been decided yet
                return 1.0
            else:
                # if all lib calls are low weights, we do not remove these lib calls
                return jaccard_similarity(set(callee_names0), set(callee_names1))
        else:
            return jaccard_similarity(tmp_callee_names0, tmp_callee_names1)

    def get_valid_functions(self):
        return self._get_valid_func_ida(0), self._get_valid_func_ida(1)

    def _rm_func_from_valid(self, func_addr, proj_id):
        self._valid_funcs[proj_id].remove(func_addr)

    def _inline_cmp_functions_without_lib_calls(self):
        fs0 = self.get_all_functions_without_lib_calls(0)
        f1_similarity_matrix = dict()
        for f_k0 in fs0:
            f1_similarity_matrix[f_k0] = dict()
            for f_k1 in self._valid_funcs[1]:
                try:
                    f1_similarity_matrix[f_k0][f_k1] = (self.cmp_caller_similarity(f_k0, f_k1, gamma=0.9))
                except InvalidFunctionException as e:
                    log.warning(str(e))
                    break
            f1_similarity_matrix[f_k0] = Detector.sort_detect_similar_func_res(f1_similarity_matrix[f_k0])
        return f1_similarity_matrix

    def cmp_bins(self, mode='ri', progress_outfile=None, not_sym_exe=False, no_skip=False):
        """
        compare 2 binaries, function by function
        here we merely compare functions being located in .text section
        `ri` is the default comparing mode
        for functions without call, we skip it temporarily
        :param progress_outfile: after search for similarity of a function of project 0, save the result progressively
                                 the content in this file will be cleared
        :return:
        """
        # clear progressive report file
        if progress_outfile is not None:
            _ = open(progress_outfile, 'w')

        log.debug("%d valid functions in %s" % (len(self._valid_funcs[0]), self._p[0].filename))
        f1_similarity_matrix = dict()
        for f_k0 in tqdm(self._valid_funcs[0], desc='comparing :'):
            f1_similarity_matrix[f_k0] = Detector.sort_detect_similar_func_res(
                self.detect_similar_func(f_k0, mode=mode, not_sym_exe=not_sym_exe, no_skip=no_skip))
            # f_k0 has finished, pop it out from cache
            # but for future comparison speed, we need to store this data later
            # if f_k0 in self._visited_RI_funcs[0].keys():
            #     self._visited_RI_funcs[0].pop(f_k0)
            if progress_outfile is not None:
                log.warning('save progressive report of function 0x%x in %s' % (f_k0, progress_outfile))
                with open(progress_outfile, 'a') as outfile:
                    self.analyse_func_detect_res(f_k0, f1_similarity_matrix[f_k0], verbose=1, outfile=outfile)

        # if self._alg == 'inline':
        #     tmp = self._inline_cmp_functions_without_lib_calls()
        #     f1_similarity_matrix.update(tmp)
        return f1_similarity_matrix

    def _get_func_addr_name_map(self, proj_id):
        f_map = dict()
        map_file = self._p[proj_id].filename + '_functions/func_map'
        if os.path.isfile(map_file):
            with open(map_file, 'r') as mf:
                offset = get_offset(self._p[proj_id])
                lines = mf.readlines()
                for line in lines:
                    tmp = line.split(' : ')
                    if len(tmp) == 2:
                        f_addr = int(tmp[0], 16)
                        f_name = tmp[1].strip()
                        f_map[f_addr + offset] = f_name
        else:
            # use angr cfg to generate the map
            for f_addr in self._valid_funcs[proj_id]:
                f_map[f_addr] = self._cfg[proj_id].functions[f_addr].name
        return f_map

    def _get_func_name_addr_map(self, proj_id):
        f_map = dict()
        map_file = self._p[proj_id].filename + '_functions/func_map'
        if os.path.isfile(map_file):
            with open(map_file, 'r') as mf:
                offset = get_offset(self._p[proj_id])
                lines = mf.readlines()
                for line in lines:
                    tmp = line.split(' : ')
                    if len(tmp) == 2:
                        f_addr = int(tmp[0], 16)
                        f_name = tmp[1].strip()
                        f_map[f_name] = offset + f_addr
        else:
            # use angr cfg to generate the map
            for f_addr in self._valid_funcs[proj_id]:
                f_map[self._cfg[proj_id].functions[f_addr].name] = f_addr
        return f_map

    @staticmethod
    def _similar_func_res_addr_to_name(res: list, f_map):
        tmp = []
        for addr, sim in res:
            tmp.append((f_map[addr], sim))
        return tmp

    @staticmethod
    def sort_detect_similar_func_res(res: dict):
        """
        The result must be the return of detect_similar_func
        Return the function address in similarity sorted order, the highest is at first
        :param res:
        """
        tmp = list(res.items())
        s = sorted(tmp, key=lambda t: t[1][1])
        return sorted(s, key=lambda t: t[1][0], reverse=True)

    def safe_cmp_func(self, start0, start1, mode='ri'):
        """
        compare 2 functions in safe mode
        :return: similarity, f0 is valid
        """
        try:
            return self.cmp_func(start0, start1, mode=mode), True
        except InvalidFunctionException as e:
            log.warning(str(e))
            if e.get_func_ptr() == start0:
                return -1.0, _invalid_difference_value, False
        except TooHardToSolveException as e:
            log.warning(str(e))
            if e.get_func_ptr() == start0:
                return -1.0, _invalid_difference_value, False
        return 0.0, _invalid_difference_value, True

    def detect_similar_func(self, start0, mode='ri', not_sym_exe=False, no_skip=False):
        """
        We compare a function in proj_0 with all functions in proj_1, and get a dictionary of
        {proj_1_func_addr: similarity}
        :param start0: the address of function in proj_0
        :return: dictionary {proj_1_func_addr: similarity}
        """
        log.info("detect similar function 0x%x in binary %s" % (start0, self._p[0].filename))
        log.info("%d valid functions in %s" % (len(self._valid_funcs[1]), self._p[1].filename))
        if start0 not in self._valid_funcs[0]:
            log.warning(str(InvalidFunctionException(start0)))
            return dict()

        comparison_res = dict()
        for start1 in self._valid_funcs[1]:
            try:
                comparison_res[start1] = self.cmp_func(start0, start1, mode=mode, not_sym_exe=not_sym_exe, no_skip=no_skip)
            except InvalidFunctionException as e:
                log.warning(str(e))
                if e.get_func_ptr() == start0:
                    # if the invalid function is the source function, we should exit the loop
                    break
                else:
                    comparison_res[start1] = (0.0, _invalid_difference_value)
            except TooHardToSolveException as e:
                log.warning(str(e))
                if e.get_func_ptr() == start0:
                    break
                else:
                    comparison_res[start1] = (0.0, _invalid_difference_value)
            except FunctionWithoutFormulaDataException as e:
                log.warning(str(e))
                if e.get_func_ptr() == start0:
                    break
                else:
                    comparison_res[start1] = (0.0, _invalid_difference_value)
        return comparison_res

    def analyse_detect_similar_func_res(self, start0, res: list):
        f_map0 = self._get_func_addr_name_map(0)
        f_map1 = self._get_func_addr_name_map(1)
        f_name = f_map0[start0]
        new_res = self._similar_func_res_addr_to_name(res, f_map1)
        match_idx = -1
        for idx in range(len(new_res)):
            if new_res[idx][0] == f_name:
                match_idx = idx
        return match_idx, (f_name, new_res)

    def analyse_func_detect_res(self, f_addr, detect_res, verbose=0, outfile=None):
        match_idx, new_detect_res = self.analyse_detect_similar_func_res(f_addr, detect_res)
        res_str = ""
        if match_idx < 0:
            res_str += '%s(0x%x) finds no counterpart\n' % (new_detect_res[0], f_addr)
        else:
            res_str += 'Match %s(0x%x) at %d (%s)\n' % \
                       (new_detect_res[0], f_addr, match_idx, str(new_detect_res[1][match_idx][1]))
        res_str += '%s : %s' % (new_detect_res[0], str(new_detect_res[1]))
        if verbose > 0:
            if outfile is None:
                print(res_str)
            else:
                outfile.write(res_str + '\n')
        return res_str

    def analyse_cmp_bins_res(self, res: dict, top_ns=None, verbose=1, output_stream=sys.stdout):
        """
        :param res: a dictionary of sorted lists (result from detect_similar_func, the sort it)
        :param top_ns:
        :param verbose:
        :return:
        """
        if top_ns is None:
            top_ns = [1, 3, 5]
        top_n_match_counts = [0 for _ in range(len(top_ns))]
        num_valid_f0 = 0
        for f_addr, detect_res in res.items():
            match_idx, new_detect_res = self.analyse_detect_similar_func_res(f_addr, detect_res)
            if verbose > 0:
                if match_idx < 0:
                    print('%s(0x%x) finds no counterpart' % (new_detect_res[0], f_addr), file=output_stream)
                else:
                    print('Match %s(0x%x) at %d (%s)' %
                          (new_detect_res[0], f_addr, match_idx, str(new_detect_res[1][match_idx][1])), file=output_stream)
                print('%s : %s' % (new_detect_res[0], str(new_detect_res[1])), file=output_stream)

            if match_idx < 0:
                continue
            else:
                if new_detect_res[1][match_idx][1][0] < 0:
                    # f0 is not a valid functions (the function is not complex enough, or too complex to angr)
                    continue
                num_valid_f0 += 1
                for idx in range(len(top_ns)):
                    if match_idx < top_ns[idx]:
                        top_n_match_counts[idx] += 1
        # if verbose > 0:
        #     for idx in range(len(top_ns)):
        #         top_n = top_ns[idx]
        #         top_n_match_count = top_n_match_counts[idx]
        #         print('Top %d match rate: %f (%d / %d)' %
        #               (top_n, top_n_match_count / num_valid_f0, top_n_match_count, num_valid_f0), file=output_stream)
        return top_n_match_counts, num_valid_f0

    def __str__(self):
        return f"{self._p[0].filename} vs. {self._p[1].filename}"


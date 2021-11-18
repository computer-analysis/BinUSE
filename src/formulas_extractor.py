import traceback
from angr import serializable
from angr.sim_options import LAZY_SOLVES, UNDER_CONSTRAINED_SYMEXEC
from src.cmp_tree import expr2tree
from src.error import InvalidLipException, TimeoutForCollectingInfoException
from src.utils import *
from src.simple_cfg import SimpleCFG
from angr.errors import AngrError
from angr.engines.successors import SimSuccessors
import claripy
from claripy.ast.bv import BV
import pickle
import signal
from contextlib import contextmanager
from collections import defaultdict
import src.config_for_sym_exe as se_config


def _set_x86_64_state_ip(state, v):
    state.regs.rip = v


def _set_x86_state_ip(state, v):
    state.regs.eip = v


def _set_aarch64_state_ip(state, v):
    state.regs.ip = v


def _reset_x86_64_state_reg(state):
    state.regs.rax = claripy.BVS('rax', size=64, explicit_name=False)


def _reset_x86_state_reg(state):
    state.regs.eax = claripy.BVS('eax', size=32, explicit_name=False)


def _reset_aarch64_state_reg(state):
    state.regs.rax = claripy.BVS('rax', size=64, explicit_name=False)


@contextmanager
def _time_limit_for_a_block(seconds, block_id):
    def signal_handler(signum, frame):
        raise TimeoutForCollectingInfoException(block_id)

    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)


class FormulaExtractor:
    SKIP_REGS = {'rflags', 'rsp', 'rbp', 'fpsw',  # x86_64
                 'ebp', 'esp', 'eflags',  # x86
                 # sp is the stack ptr, others are register for special usage.
                 # nzcv is used as flag registers https://developer.arm.com/docs/ddi0595/b/aarch64-system-registers/nzcv
                 'sp', 'x8', 'x16', 'x17', 'x18', 'x29', 'x30', 'nzcv', 'xzr', 'wzr'  # aarch64
                 }
    AMD64_SKIP_REGS = {'rflags', 'rsp', 'rbp', 'fpsw'}
    X86_SKIP_REGS = {'ebp', 'esp', 'eflags'}
    AARCH64_SKIP_REGS = {'sp', 'x8', 'x16', 'x17', 'x18', 'x29', 'x30', 'nzcv', 'xzr', 'wzr'}

    AMD64_RET_REGS = {'rax'}
    X86_RET_REGS = {'eax'}
    AARCH64_RET_REGS = {'x0', 'x1', 'x2', 'x3', 'x4', 'x5', 'x6', 'x7'}

    AMD64_CALL_ARGS_REGS = {'rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9', 'edi', 'esi', 'edx', 'ecx'}
    X86_CALL_ARGS_REGS = {'edx', 'ecx'}
    AARCH64_CALL_ARGS_REGS = {'x0', 'x1', 'x2', 'x3', 'x4', 'x5', 'x6', 'x7'}

    def __init__(self, p: angr.Project, cfg=None, mode='ted', filter_assignment=True,
                 state_options=(UNDER_CONSTRAINED_SYMEXEC, LAZY_SOLVES), no_constraints=False,
                 time_limit=60):
        self._p = p
        self._cfg = cfg
        # if self._cfg is None:
        #     self._cfg = self._p.analyses.CFGFast()
        self._mode = mode
        self._transform_func = None

        #  clear all constraints in state.solver.constraints after every step
        self._no_constraints = no_constraints

        # time limit for getting info from a single block (basic block or RI block)
        self._time_limit = time_limit

        if self._mode == 'ted':
            self._transform_func = self._transform_to_ted_format
        elif self._mode == 'smt':
            self._transform_func = self._transform_to_smt_format
        self._state_options = list(state_options)

        self._filter_assignment = filter_assignment
        self._visited = dict()
        self._visited_smt = dict()
        self._visited_ci = dict()
        self._ignore_subgraph_roots = dict()

        self._executable_ranges = get_executable_ranges(self._p)
        self._data_ranges = get_data_ranges(self._p)
        self._obj_ranges = get_obj_ranges(self._p)

        self._set_state_ip_func = None
        self._get_se_info_func = None
        self._reset_state_return_reg_func = None
        self._ptr_size = 64
        self._skip_regs = FormulaExtractor.SKIP_REGS

        if self._p.arch.name == 'AMD64':
            self._set_state_ip_func = _set_x86_64_state_ip
            self._reset_state_return_reg_func = _reset_x86_64_state_reg
            self._skip_regs = FormulaExtractor.AMD64_SKIP_REGS
            self._return_regs = FormulaExtractor.AMD64_RET_REGS
            # ignore the return value currently, since we cannot tell whether the function really returns
            # self._return_regs = set()
            self._call_args_regs = FormulaExtractor.AMD64_CALL_ARGS_REGS
            self._get_se_info_func = self._get_amd64_se_info
            self._ptr_size = 64
        elif self._p.arch.name == 'X86':
            self._set_state_ip_func = _set_x86_state_ip
            self._reset_state_return_reg_func = _reset_x86_state_reg
            self._skip_regs = FormulaExtractor.X86_SKIP_REGS
            self._return_regs = FormulaExtractor.X86_RET_REGS
            self._call_args_regs = FormulaExtractor.X86_CALL_ARGS_REGS
            self._get_se_info_func = self._get_x86_se_info
            self._ptr_size = 32
        elif self._p.arch.name == 'AARCH64':
            self._set_state_ip_func = _set_aarch64_state_ip
            self._reset_state_return_reg_func = _reset_aarch64_state_reg
            self._skip_regs = FormulaExtractor.AARCH64_SKIP_REGS
            self._return_regs = FormulaExtractor.AARCH64_RET_REGS
            self._call_args_regs = FormulaExtractor.AARCH64_CALL_ARGS_REGS
            self._get_se_info_func = self._get_regs_se_info
            self._ptr_size = 64
        else:
            log.error("Untested arch!")
            assert False

    @property
    def ptr_size(self):
        return self._ptr_size

    def save_visit_data(self, save_path):
        with open(save_path, 'wb') as f:
            pickle.dump({
                'visited': self._visited,
                'visited_smt': self._visited_smt,
                'visited_ci': self._visited_ci
            }, f)

    def load_visit_data(self, save_path):
        with open(save_path, 'rb') as f:
            tmp = pickle.load(f)
            self._visited = tmp['visited']
            self._visited_smt = tmp['visited_smt']
            self._visited_ci = tmp['visited_ci']

    def _get_blank_state(self, addr):
        return self._p.factory.blank_state(addr=addr,
                                           add_options=self._state_options
                                           )

    def _ignore_subgraph_of_root_block(self, rib: tuple):
        if rib[0] in self._ignore_subgraph_roots.keys():
            self._ignore_subgraph_roots[rib[0]] += 1
        else:
            self._ignore_subgraph_roots[rib[0]] = 1

    def _initialize_block_as_empty(self, block_id):
        self._visited[block_id] = ([], [], set())

    def get_formulas_from(self, block_id, callees=None):
        log.debug('try to get formulas from RIB: %s' % str(block_id))
        try:
            with _time_limit_for_a_block(self._time_limit, block_id):
                if isinstance(block_id, int):
                    return self._get_formulas_from(block_id)
                else:
                    return self._get_formulas_from_rib(block_id, callees)
        except InvalidLipException as e:
            log.error(str(e))
        except TimeoutForCollectingInfoException as e:
            log.error(str(e))
        except Exception as e:
            log.error(str((self._p.filename, block_id)) + ' meets angr error: ' + str(e))
            # it is likely we will meet angr error again
            if isinstance(block_id, tuple):
                self._ignore_subgraph_of_root_block(block_id)
        self._initialize_block_as_empty(block_id)
        return self._visited[block_id]

    def _sym_exe_block(self, block_id):
        # the block_id must have been checked
        tmp_state = self._get_blank_state(block_id)
        return tmp_state.step(), tmp_state

    @staticmethod
    def transform_to_ted_format(formulas, constraints, read_from, exe_ranges, data_ranges):
        ted_formulas = []
        ted_constraints = []
        for f in formulas:
            ted_formulas.append((f[0], expr2tree(f[1], exe_ranges, data_ranges)))
        for c in constraints:
            ted_constraints.append(expr2tree(c, exe_ranges, data_ranges))
        read_from = {str(element) for element in read_from}
        return ted_formulas, ted_constraints, read_from

    @staticmethod
    def transform_to_smt_format(formulas, constraints, read_from, exe_ranges, data_ranges, obj_ranges, ptr_size,
                                final_state):
        const_data_ptr = claripy.BVV(0xfffffe, ptr_size)
        const_func_ptr = claripy.BVV(0x400001, ptr_size)
        const_obj_ptr = claripy.BVV(0x400002, ptr_size)
        const_stack_ptr = claripy.BVV(0x400003, ptr_size)

        if ptr_size == 32:
            stack_min_addr = se_config.MIN_SP_VALUE_32
            stack_max_addr = se_config.MAX_SP_VALUE_32
        elif ptr_size == 64:
            stack_min_addr = se_config.MIN_SP_VALUE_64
            stack_max_addr = se_config.MAX_SP_VALUE_64

        def replace_ptr_value(f, recursion_depth):
            if not (hasattr(f, 'depth') and hasattr(f, 'args')):
                return f
            if f.depth == 1 and f.op == 'BVV':
                if in_ranges(f.args[0], exe_ranges) and f.args[1] == ptr_size:
                    return const_func_ptr
                elif in_ranges(f.args[0], data_ranges) and f.args[1] == ptr_size:
                    return const_data_ptr
                elif in_ranges(f.args[0], obj_ranges) and f.args[1] == ptr_size:
                    return const_obj_ptr
                elif stack_max_addr > f.args[0] >= stack_min_addr and f.args[1] == ptr_size:
                    # We use this simple method to tackle with it, no matter whether the memaddr plugin is used
                    return const_stack_ptr
            elif f.depth > 1:
                if final_state is not None and hasattr(final_state, 'memaddr'):
                    # we use a plugin to record all symbols which is used as a memory pointer
                    # if the a constraint in the final state looks like <bool A == 0x777> and A is a memory pointer,
                    # we transform <bool A == 0x777> to <bool A == stack_ptr>
                    if f.op == '__eq__' and f.args[0].symbolic and not f.args[1].symbolic \
                            and final_state.memaddr.has(f.args[0]):
                        if f.depth == 2:
                            return f.args[0] == const_stack_ptr
                        elif f.depth > 2:
                            # f.args[0] could be very complex, we need transform it
                            return replace_ptr_value(f.args[0], recursion_depth + 1) == const_stack_ptr
                new_args = [replace_ptr_value(arg, recursion_depth + 1) for arg in f.args]
                f.args = tuple(new_args)
            return f

        smt_formulas, smt_constraints = [], []
        bvs_dict = dict()
        for f in formulas:
            # print('old: ' + str(f[1]))
            tmp_f = replace_ptr_value(f[1], 0)
            # tmp_f = FormulaExtractor.extend_BV32_to_BV64(tmp_f, bvs_dict)
            smt_formulas.append((f[0], tmp_f))
            # print('new: ' + str(smt_formulas[-1][1]))
        for c in constraints:
            tmp_c = replace_ptr_value(c, 0)
            # tmp_c = FormulaExtractor.extend_BV32_to_BV64(tmp_c, bvs_dict)
            smt_constraints.append(tmp_c)
        return smt_formulas, [claripy.And(*smt_constraints)], read_from

    @staticmethod
    def extend_BV32_to_BV64(f, bvs_dict):
        is_bv = isinstance(f, claripy.ast.bv.BV)
        is_bool = isinstance(f, claripy.ast.bool.Bool)
        if not is_bv and not is_bool:
            return f
        if f.depth == 1:
            if isinstance(f, claripy.ast.bv.BV) and f.size() == 32:
                if f.symbolic:
                    f_name = str(f._encoded_name, 'utf8')
                    f_name = f_name[:f_name.rfind('_')]
                    f_name = f_name[:f_name.rfind('_')]
                    if f_name not in bvs_dict:
                        bvs_dict[f_name] = claripy.BVS(name=f_name, size=64)
                    return bvs_dict[f_name]
                else:
                    if f.args[0] & (1 << 31):
                        return claripy.BVV(0xffffffff00000000 | f.args[0], 64)
                    else:
                        return claripy.BVV(f.args[0], 64)
            else:
                return f
        elif f.depth == 2 and f.op == 'Extract' and f.args[2].symbolic and f.args[2].size() == 32:
            # an Extract is regarded as a leaf node
            return claripy.Extract(f.args[0], f.args[1], FormulaExtractor.extend_BV32_to_BV64(f.args[2], bvs_dict))
        elif f.op == 'Concat':
            # we make sure that Concat will not change the size of f
            new_args = []
            for arg in f.args:
                tmp = FormulaExtractor.extend_BV32_to_BV64(arg, bvs_dict)
                # we Extract the corresponding bits
                tmp = claripy.Extract(arg.size() - 1, 0, tmp)
                new_args.append(tmp)
            return claripy.Concat(*new_args)
        elif hasattr(f, 'args') and hasattr(f, 'size'):
            # many binary op requires same size of left hand side and right hand side
            # if LHS and RHS are 32 bits, we turn both side into 64 bits
            new_args = []
            all_same_size = True
            for i in range(len(f.args) - 1):
                if not hasattr(f.args[i], 'size') or not hasattr(f.args[i + 1], 'size') \
                        or f.args[i].size() != f.args[i + 1].size():
                    all_same_size = False
                    break
            if f.op.startswith('__') and all_same_size:
                new_args = [FormulaExtractor.extend_BV32_to_BV64(f.args[idx], bvs_dict) for idx in range(len(f.args))]
                # we simply think LHS and RHS mush have same size
                if f.args[0].size() == 32:
                    # we extend the size to 64 bits
                    for idx in range(len(f.args)):
                        if new_args[idx].size() < 64:
                            new_args[idx] = claripy.Concat(claripy.BVV(0, 64 - new_args[idx].size()), new_args[idx])
                else:
                    # we make sure the size has not been changed
                    for idx in range(len(f.args)):
                        if new_args[idx].size() > f.args[idx].size():
                            new_args[idx] = claripy.Extract(f.args[idx].size() - 1, 0, new_args[idx])
                        elif new_args[idx].size() < f.args[idx].size():
                            new_args[idx] = claripy.Concat(claripy.BVV(0, f.args[idx].size() - new_args[idx].size()),
                                                           new_args[idx])
            else:
                for arg in f.args:
                    new_args.append(FormulaExtractor.extend_BV32_to_BV64(arg, bvs_dict))
            if is_bv:
                f = claripy.ast.BV(op=f.op, args=tuple(new_args), length=64)
            elif is_bool:
                f = claripy.ast.Bool(op=f.op, args=tuple(new_args))
            return f
        else:
            new_args = []
            for arg in f.args:
                new_args.append(FormulaExtractor.extend_BV32_to_BV64(arg, bvs_dict))
            if is_bv:
                f = claripy.ast.BV(op=f.op, args=tuple(new_args), length=64)
            elif is_bool:
                f = claripy.ast.Bool(op=f.op, args=tuple(new_args))
            return f

    def _transform_to_ted_format(self, formulas, constraints, read_from, **kwargs):
        fs, c, r = FormulaExtractor.transform_to_ted_format(formulas, constraints, read_from,
                                                            self._executable_ranges, self._data_ranges)
        # filter assignment
        new_fs = []
        for f in fs:
            if len(f[1].children) == 0 and isinstance(f[1].label, str) \
                    and ('reg' in f[1].label or 'mem' in f[1].label):
                continue
            new_fs.append(f)
        return new_fs, c, r

    def _transform_to_smt_format(self, formulas, constraints, read_from, **kwargs):
        final_state = kwargs.get('final_state', None)
        fs, c, r = FormulaExtractor.transform_to_smt_format(formulas, constraints, read_from,
                                                            self._executable_ranges, self._data_ranges,
                                                            self._obj_ranges, self._ptr_size, final_state)
        return fs, c, r

    @staticmethod
    def _filter_assigning(formulas):
        res = []
        for f in formulas:
            if is_assigning_value(f[1]):
                continue
            res.append(f)
        return res

    def _filter_invalid_constraints(self, constraints):
        # I add this function because of angr's bug, it may introduce wrong constraints
        res = []
        for c in constraints:
            valid = True
            if c.depth == 1 and c.op == 'BoolV' and c.args == (True,):
                # add redundant True constraints, <Bool True>
                valid = False
            else:
                all_inputs = get_expression_input(c, with_extract=False)
                for i in all_inputs:
                    name = angr_symbolic_name(i)
                    if name in self._skip_regs:
                        valid = False
                        break
            if valid:
                res.append(c)
        return res

    @staticmethod
    def get_se_info(sucs, reg_records: set, mem_records: set, init_state=None):
        formulas = []
        constraints = []
        read_from = set()
        for c in sucs.all_successors[0].solver.constraints:
            e = claripy.simplify(c)
            read_from.update(get_expression_input(e))
            constraints.append(e)

        # read formulas from registers
        if len(sucs.flat_successors) > 0:
            for reg_name in reg_records:
                f = claripy.simplify(getattr(sucs.flat_successors[0].regs, reg_name))
                read_from.update(get_expression_input(f))
                formulas.append((reg_name, f))
        elif len(sucs.unconstrained_successors) > 0:
            # sometimes the next instruction address is hard to decide, then next states are in unconstrained stash
            for reg_name in reg_records:
                f = claripy.simplify(getattr(sucs.unconstrained_successors[0].regs, reg_name))
                read_from.update(get_expression_input(f))
                formulas.append((reg_name, f))

        # read formulas from memory
        if init_state is not None and len(mem_records) > 0:
            formulas.extend(FormulaExtractor.get_writing_mem_formulas(init_state, sucs.all_successors[0], mem_records))
        return formulas, constraints, read_from

    @staticmethod
    def get_writing_reg_record(block, arch_name, valid_instrs=None):
        insns = block.capstone.insns
        write_records = set()
        # use proper set of skip regs
        skip_regs = FormulaExtractor.SKIP_REGS
        if arch_name == 'AMD64':
            skip_regs = FormulaExtractor.AMD64_SKIP_REGS
        elif arch_name == 'X86':
            skip_regs = FormulaExtractor.X86_SKIP_REGS
        elif arch_name == 'AARCH64':
            skip_regs = FormulaExtractor.AARCH64_SKIP_REGS

        for insn in insns:
            # check the address is valid (only use registers for converting arguments)
            if valid_instrs is not None and insn.address not in valid_instrs:
                continue
            read_regs, write_regs = insn.insn.regs_access()
            for reg_id in write_regs:
                if insn.insn.reg_name(reg_id) in skip_regs:
                    continue
                write_records.add(insn.insn.reg_name(reg_id))
        return write_records

    def _get_writing_reg_record(self, block_id):
        block = self._p.factory.block(block_id)
        return FormulaExtractor.get_writing_reg_record(block, self._p.arch.name)

    def get_write_regs(self, rib: tuple):
        write_records = set()
        for b_id in rib:
            write_records.update(self._get_writing_reg_record(b_id))
        return write_records

    def get_rib_args_addr(self, rib: tuple, callees):
        """
        return the type of the rib
        :param rib:
        :param callees:
        :return: is_call, is_ret, (callee_entry, callee_args_addrs)
        """
        last_block = self._p.factory.block(rib[-1])
        end_instr_addr = last_block.instruction_addrs[-1]
        if callees and end_instr_addr in callees.keys():
            # the rib ends with call
            return True, False, callees[end_instr_addr]
        elif 'call' in last_block.capstone.insns[-1].insn.mnemonic:
            return True, False, (int(last_block.capstone.insns[-1].insn.op_str, 16), None)
            # try:
            #     return True, False, (int(last_block.capstone.insns[-1].insn.op_str, 16), None)
            # except ValueError:
            #     return False, False, None
        elif 'ret' in last_block.capstone.insns[-1].insn.mnemonic:
            return False, True, None
        else:
            return False, False, None

    @staticmethod
    def get_writing_mem_formulas(old_state, new_state, valid_mem_addrs: set = None):
        if valid_mem_addrs is None or len(valid_mem_addrs) == 0:
            changed_mem_addr_set = new_state.memory.changed_bytes(old_state.memory)
        else:
            # the memory needs to be read is fixed
            changed_mem_addr_set = valid_mem_addrs
        # here are changed bytes, we need to merge continuous bytes.
        # fortunately, angr symbolizes the bytes being used in continuous way.
        formulas = []
        # continuous bytes use the same formula, save the string in right_side to avoid redundancy.
        right_sides = set()
        for addr in changed_mem_addr_set:
            if valid_mem_addrs and addr not in valid_mem_addrs:
                continue
            if new_state.memory.mem[addr] is None:
                continue
            # the changed value is in mem[addr].object, use ('mem_%x' % addr) as the left side of equations
            if str(new_state.memory.mem[addr].object) in right_sides:
                continue
            right_sides.add(str(new_state.memory.mem[addr].object))
            left_side_name = 'mem_%x' % addr
            # because of big and little end arch, the mem may have 'Reverse' operation at the very beginning. Ignore it.
            right_side_ast = new_state.memory.mem[addr].object
            # if the first op is Reverse, this means this memory points to an object with more than 1 bytes
            # we only use the formulas, so we simply remove this Reverse
            if right_side_ast.op == 'Reverse':
                right_side_ast = right_side_ast.args[0]
            # if the project is little end, we need to reverse the constant value
            if right_side_ast.depth == 1 and isinstance(right_side_ast, BV) and not right_side_ast.symbolic:
                right_side_ast = claripy.Reverse(right_side_ast)
            formulas.append((left_side_name, right_side_ast))
        return formulas

    def _get_formulas_from(self, block_id):
        if block_id in self._visited:
            return self._visited[block_id]
        if self._p.factory.block(block_id):
            write_records = self._get_writing_reg_record(block_id)
            sucs, init_state = self._sym_exe_block(block_id)
            formulas, constraints, read_from = self.get_se_info(sucs, write_records, set(), init_state)

            # filter out the formulas which is merely assigning value
            if self._filter_assignment:
                formulas = self._filter_assigning(formulas)

            # the transform function, adapt the format
            self._visited[block_id] = self._transform_func(formulas, constraints, read_from)
            return self._visited[block_id]
        else:
            assert False, 'invalid block id'

    def _sym_exe_rib(self, lip: tuple):
        init_state = self._get_blank_state(lip[0])
        bb_idx = 1
        state = init_state
        while bb_idx < len(lip):
            b_id = lip[bb_idx]
            bb_idx += 1
            sucs = state.step()
            former_block_addr = state.addr
            former_block_size = self._p.factory.block(state.addr).size
            state = None
            for tmp_s in sucs.flat_successors:
                if tmp_s.addr == b_id:
                    state = tmp_s
                    break
            # the state may have go further than b_id, in this case we try to find a successor in lip
            if state is None and 0 <= b_id - former_block_addr < former_block_size:
                for tmp_s in sucs.flat_successors:
                    if tmp_s.addr in lip[bb_idx:]:
                        bb_idx = lip.index(tmp_s.addr) + 1
                        state = tmp_s
                        break
            if state is None:
                if len(sucs.flat_successors) > 0:
                    state = sucs.flat_successors[0]
                    log.debug('cannot find proper successors 0x%x in %s' % (b_id, str(lip)))
                elif len(sucs.unconstrained_successors) > 0:
                    state = sucs.unconstrained_successors[0]
                    log.debug('use unconstrained successive 0x%x in %s' % (b_id, str(lip)))
                elif len(sucs.all_successors) > 0:
                    state = sucs.all_successors[0]
                    log.debug('use unsatisfied successive 0x%x in %s' % (b_id, str(lip)))
                else:
                    raise InvalidLipException(lip, b_id)
                self._set_state_ip_func(state, b_id)
                # remove the constraints of it, since the constraints is not correct for this path
                state.solver.constraints.clear()
            if self._no_constraints:
                # clear all constraints anyway
                state.solver.constraints.clear()
        return state.step(), init_state

    def update_visited_cache(self, cache: dict):
        self._visited.update(cache)

    def _is_return_rib(self, rib):
        last_block = self._p.factory.block(addr=rib[-1])
        last_instr = get_block_last_insn(last_block)
        return is_ret_instr(last_instr)

    def _get_regs_se_info(self, sucs, rib: tuple, init_state, callees=None, **kwargs):
        reg_records = kwargs.get('reg_read', set())
        mem_records = set()
        if reg_records is None:
            return self.get_se_info(sucs, set(), mem_records, init_state)
        if len(reg_records) == 0:
            reg_records = self.get_write_regs(rib)
        return self.get_se_info(sucs, reg_records, mem_records, init_state)

    def _get_amd64_se_info(self, sucs, rib: tuple, init_state, callees, **kwargs):
        reg_records = kwargs.get('reg_read', set())
        mem_records = set()

        if reg_records is None:
            # here we merely collect constraints
            return self.get_se_info(sucs, set(), mem_records, init_state)

        if reg_records:
            # the registers to be read have been determined
            return self.get_se_info(sucs, reg_records, mem_records, init_state)

        if callees is None:
            reg_records = self.get_write_regs(rib)
        else:
            is_call, is_ret, callee = self.get_rib_args_addr(rib, callees)
            if is_call:
                # a call is matched
                callee_entry, args_relative_instr_list = callee
                if args_relative_instr_list is None or len(args_relative_instr_list) == 0:
                    # something wrong with IDA or a function without arguments, return to the write_records situation
                    reg_records = self.get_write_regs(rib)
                else:
                    for b_id in reversed(rib):
                        block = self._p.factory.block(addr=b_id)
                        reg_records.update(FormulaExtractor.get_writing_reg_record(block, self._p.arch.name,
                                                                                   args_relative_instr_list))
                        if len(reg_records) == len(args_relative_instr_list):
                            break
            elif is_ret:
                reg_records = self._return_regs
                # reg_records = self.get_write_regs(rib)
            else:
                # unknown root instruction, return to the write_records situation
                reg_records = self.get_write_regs(rib)
        # for amd64 arch, we merely check the first 6 arguments for a function call
        # if it is return, we read from rax/eax
        if self._is_return_rib(rib):
            tmp = reg_records.intersection(self._return_regs)
        else:
            tmp = reg_records.intersection(self._call_args_regs)
        if len(tmp) > 0:
            # if there is no formulas in this block, we still use the records of all registers being written
            reg_records = tmp
        # reg_records = tmp
        if len(reg_records) == 0:
            reg_records = self.get_write_regs(rib)

        return self.get_se_info(sucs, reg_records, mem_records, init_state)

    def _get_x86_se_info(self, sucs, rib: tuple, init_state, callees, **kwargs):
        reg_records = set()
        mem_records = kwargs.get('mem_read', set())
        final_state = sucs.all_successors[0]
        if mem_records is None:
            # no argument
            return self.get_se_info(sucs, reg_records, set(), init_state)
        elif len(mem_records) == 0:
            esp_v = final_state.solver.eval(final_state.regs.esp)
            mem_records.add(esp_v + 4)
            mem_records.add(esp_v + 8)
        if mem_records:
            # the memory to be read has been determined
            return self.get_se_info(sucs, reg_records, mem_records, init_state)

        if callees is None:
            reg_records = self.get_write_regs(rib)
        else:
            is_call, is_ret, callee = self.get_rib_args_addr(rib, callees)
            if is_call:
                callee_entry, args_relative_instr_list = callee
                if args_relative_instr_list is not None and len(args_relative_instr_list) > 0:
                    # the arguments stores on stack
                    num_args = len(args_relative_instr_list)
                    esp_value = sucs.all_successors[0].solver.eval(sucs.all_successors[0].regs.esp)
                    mem_records = set([esp_value - i * 4 for i in range(num_args)])
                else:
                    reg_records = self.get_write_regs(rib)
            elif is_ret:
                reg_records = self._return_regs
            else:
                reg_records = self.get_write_regs(rib)
        return self.get_se_info(sucs, reg_records, mem_records, init_state)

    def _cache_formuals_from_sucs(self, sucs, rib: tuple, init_state, callees, **kwargs):

        formulas, constraints, read_from = self._get_se_info_func(sucs, rib, init_state, callees, **kwargs)
        self._visited_smt[rib] = (formulas, constraints, read_from)

        # filter out the formulas which is merely assigning value
        if self._filter_assignment:
            formulas = self._filter_assigning(formulas)

        constraints = self._filter_invalid_constraints(constraints)

        # the transform function, adapt the format
        self._visited[rib] = self._transform_func(formulas, constraints, read_from, final_state=sucs.all_successors[0])

    def cache_formulas_from_state(self, state, rib: tuple, init_state, callees, **kwargs):
        sucs = SimSuccessors(init_state.addr, initial_state=init_state)
        sucs.all_successors.append(state)
        sucs.flat_successors.append(state)
        self._cache_formuals_from_sucs(sucs, rib, init_state, callees, **kwargs)

    def cache_constraint_from_state(self, state, rib: tuple, init_state, **kwargs):
        # for return path, we only collect the constraints
        # since we do not know whether the return register is meaningful
        if rib[-1] is not None:
            raise NotImplementedError("This is only used for unconstrained states")
        sucs = SimSuccessors(init_state.addr, initial_state=init_state)
        sucs.all_successors.append(state)
        sucs.flat_successors.append(state)
        tmp_rib = rib[:-1]
        self._cache_formuals_from_sucs(sucs, tmp_rib, init_state, None,
                                       reg_read=self._return_regs,
                                       mem_read=set())
        if tmp_rib in self._visited and isinstance(self._visited[tmp_rib], tuple):
            self._visited[rib] = ([], self._visited[tmp_rib][1], self._visited[tmp_rib][2])
            self._visited.pop(tmp_rib)

    def _get_formulas_from_rib(self, rib: tuple, callees=None):
        """
        Get the formulas from a list of blocks
        :param rib: The type is tuple, so that it can be used as id of a dictionary
                    The lip denotes linearly independent path, it is a list of blocks
                    The lips here is merely a part of the whole lip
                    The end block of lip usually contains root instruction
        :return:
        """
        if rib in self._visited:
            if self._visited[rib] is None:
                self._initialize_block_as_empty(rib)
            return self._visited[rib]
        if rib[0] in self._ignore_subgraph_roots.keys() and self._ignore_subgraph_roots[rib[0]] > 2:
            self._initialize_block_as_empty(rib)
            return self._visited[rib]
        log.debug('collect formulas from RIB: %s' % str(rib))
        sucs, init_state = self._sym_exe_rib(rib)
        self._cache_formuals_from_sucs(sucs, rib, init_state, callees)
        log.debug('RIB %s formulas: %s' % (str(rib), str(self._visited_smt[rib][0])))
        log.debug('RIB %s constraints: %s' % (str(rib), str(self._visited_smt[rib][1])))
        log.debug('RIB %s read from: %s' % (str(rib), str(self._visited[rib][2])))
        return self._visited[rib]

    def clear_cache(self):
        self._visited.clear()

    def __str__(self):
        res = ''
        for block_id, node in self._visited.items():
            formulas, constraints = node
            res += '%d:\n' % block_id
            res += 'formulas:\n'
            for f in formulas:
                res += 'f  %s = %s\n' % (f[0], str(f[1]))
            res += 'constraints:\n'
            for c in constraints:
                res += 'c  ' + str(c) + '\n'
        return res

import z3
import claripy
from claripy.backends.backend_z3 import BackendZ3
from itertools import permutations
from src.utils import get_expression_input, remove_extract
from src.error import TooManyVariables4Comparison
from src.utils import log


class _MyBackendZ3(BackendZ3):
    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        if len(extra_constraints) > 0:
            solver.push()
            solver.add(*extra_constraints)

        try:
            tmpsol = z3.Solver(ctx=self._context)
            tmpsol.set('timeout', 15000)
            tmpsol.add(solver.assertions())
            if tmpsol.check() != z3.sat:
                return False
            if model_callback is not None:
                model_callback(self._generic_model(tmpsol.model()))
        finally:
            if len(extra_constraints) > 0:
                solver.pop()
        return True


def ne_formulas(f1, f2):
    if isinstance(f1, claripy.ast.bv.BV) and isinstance(f2, claripy.ast.bv.BV):
        if f1.size() == f2.size():
            return claripy.ast.Bool(op='__ne__', args=(f1, f2))
        elif f1.size() == 32 and f2.size() == 64:
            # only 32 bits and 64 bits formulas will use Extract
            return claripy.ast.Bool(op='__ne__', args=(f1, claripy.Extract(31, 0, f2)))
        elif f1.size() == 64 and f2.size() == 32:
            return claripy.ast.Bool(op='__ne__', args=(claripy.Extract(31, 0, f1), f2))
        else:
            return None
    elif isinstance(f1, claripy.ast.bool.Bool) and isinstance(f2, claripy.ast.bool.Bool):
        return claripy.ast.Bool(op='__ne__', args=(f1, f2))
    else:
        raise NotImplementedError()


loose_BV_sizes = [1, 8, 16, 32, 64]


def eq_var(v1, v2):
    if isinstance(v1, claripy.ast.bv.BV) and isinstance(v2, claripy.ast.bv.BV):
        v1_size = v1.size()
        v2_size = v2.size()
        if v1_size == v2_size:
            return claripy.ast.Bool(op='__eq__', args=(v1, v2))
        elif v1_size in loose_BV_sizes and v2_size in loose_BV_sizes:
            if v1_size < v2_size:
                return claripy.And(claripy.ast.Bool(op='__eq__', args=(v1, claripy.Extract(v1_size - 1, 0, v2))),
                                   v2[v2_size - 1:v1_size] == 0)
            else:
                return claripy.And(claripy.ast.Bool(op='__eq__', args=(claripy.Extract(v2_size - 1, 0, v1), v2)),
                                   v1[v1_size - 1:v2_size] == 0)
        else:
            return None
    elif isinstance(v1, claripy.ast.bool.Bool) and isinstance(v2, claripy.ast.bool.Bool):
        return claripy.ast.Bool(op='__eq__', args=(v1, v2))
    else:
        raise NotImplementedError()


def get_var_constraints(input1, input2):
    if len(input1) != len(input2):
        raise NotImplementedError()
    constraints = []
    is_valid_permutation = True
    for idx in range(len(input1)):
        tmp = eq_var(input1[idx], input2[idx])
        if tmp is None:
            is_valid_permutation = False
            break
        constraints.append(tmp)
    if is_valid_permutation:
        return constraints
    else:
        return None


def may_check_nullptr(c, ptr_size):
    if isinstance(c, claripy.ast.bool.Bool):
        if c.op == 'Not' and c.depth == 3:
            c = c.args[0]
            if c.op == '__eq__':
                if isinstance(c.args[0], claripy.ast.bv.BV) and isinstance(c.args[1], claripy.ast.bv.BV) \
                        and c.args[0].symbolic and not c.args[1].symbolic:
                    # NULL is 0 for C code
                    # the size must be pointer's size
                    return c.args[1].args[0] == 0 and c.args[1].args[1] == ptr_size
    return False


def ignore_null_check(f, ptr_size):
    """
    f is a formula, with if condition
    replace the constraints of f
    """
    if f.op == 'If':
        condition = f.args[0]
        new_condition = []
        if condition.op == 'And':
            for c in condition.args:
                # log.debug((c, c.op, c.args))
                if not may_check_nullptr(c, ptr_size):
                    new_condition.append(c)
            if len(new_condition) == len(condition.args):
                return None
            else:
                if new_condition:
                    return claripy.If(claripy.And(*new_condition),
                                      f.args[1],
                                      f.args[2])
                else:
                    return f.args[1]
        else:
            if not may_check_nullptr(condition, ptr_size):
                return None
            else:
                return f.args[1]


def check_if_inputs_match(f1, f2, equal_var):
    input1 = get_expression_input(f1)
    input2 = get_expression_input(f2)
    input1 = list(input1)
    input2 = list(input2)
    if equal_var and len(input1) != len(input2):
        # tentatively we treat expressions with different number of inputs as different, we do not prove
        input1 = list(remove_extract(input1))
        input2 = list(remove_extract(input2))
        if len(input1) != len(input2):
            log.debug(f'diff # inputs {len(input1)} and {len(input2)}')
            log.debug(input1)
            log.debug(input2)
    return input1, input2


def check_and_return_formula_pair_with_inputs(f1, f2, ptr_size1, ptr_size2):
    input1, input2 = check_if_inputs_match(f1, f2, True)
    # if len(input1) != len(input2):
    #     return False
    if len(input1) != len(input2):
        f1 = ignore_null_check(f1, ptr_size1)
        f2 = ignore_null_check(f2, ptr_size2)
        if f1 is None or f2 is None:
            return None, None
        log.debug(f'Ignore null check {str(f1)} {str(f2)}')
        input1, input2 = check_if_inputs_match(f1, f2, True)
        if len(input1) != len(input2):
            return None, None
    return (f1, input1), (f2, input2)


def factorial(n):
    res = 1
    while n > 1:
        res *= n
        n -= 1
    return res


def prove_equal(merged_f1, merged_f2, ptr_size1, ptr_size2, c1=None, c2=None, cmp_limit=120, equal_var=True):
    """
    prove f1 == f2, using SMT solver Z3
    :param f1:
    :param f2:
    :param c1: extra-constraints of f1
    :param c2: extra-constraints of f2
    :return:
    """
    log.debug('prove_equal')
    f1, orig_f1 = merged_f1
    f2, orig_f2 = merged_f2
    if c1 is not None and c2 is not None:
        if len(c1) > 0 and len(c2) > 0:
            solver = claripy.Solver(backend=_MyBackendZ3())
            # our normalization may make the constraints become UNSAT, ignore it when it happens
            try:
                if not solver.satisfiable(c1) or not solver.satisfiable(c2):
                    f1 = orig_f1
                    f2 = orig_f2
                    c1 = None
                    c2 = None
            except Exception:
                f1 = orig_f1
                f2 = orig_f2
                c1 = None
                c2 = None

    # ne_f1_f2 = ne_formulas(f1, f2)
    # if ne_f1_f2 is None:
    #     log.debug("fail1 to create not_equal formula")
    #     log.debug(f1)
    #     log.debug(f2)
    #     return False
    f1_in1, f2_in2 = check_and_return_formula_pair_with_inputs(f1, f2, ptr_size1, ptr_size2)
    if f1_in1 is None or f2_in2 is None:
        log.debug('inputs variables do not match')
        return False
    f1, input1 = f1_in1
    f2, input2 = f2_in2
    ne_f1_f2 = ne_formulas(f1, f2)
    if ne_f1_f2 is None:
        log.debug("fail to create not_equal formula")
        log.debug(f1)
        log.debug(f2)
        return False
    log.debug(f"To prove {str(ne_f1_f2)} UNSAT")

    count = 0
    min_num_var = min(len(input1), len(input2))
    if min_num_var == 0:
        # this means no extra-constraints should be added, input1 or input2 is a constant
        solver = claripy.Solver(backend=_MyBackendZ3())
        solver.add(ne_f1_f2)
        return not solver.satisfiable()

    if factorial(min_num_var) > cmp_limit:
        raise TooManyVariables4Comparison(f1, f2, cmp_limit)

    for in1 in permutations(input1, min_num_var):
        constraints = []
        count += 1
        if count > cmp_limit:
            raise TooManyVariables4Comparison(f1, f2, cmp_limit)
        try:
            constraints = get_var_constraints(in1, input2[:min_num_var])
            if constraints is None:
                continue
            cmp_expr = ne_f1_f2
            # print(str(constraints))
            # print(str(cmp_expr))

            # if we have extra constraints, we need to ensure that constraints can be satisfied first
            need_pre_condition_sat_check = False
            if c1 is not None:
                need_pre_condition_sat_check = True
                constraints.extend(c1)
            if c2 is not None:
                need_pre_condition_sat_check = True
                constraints.extend(c2)

            if need_pre_condition_sat_check:
                solver = claripy.Solver(backend=_MyBackendZ3())
                # check the constraints first
                solver.add(constraints)
                if not solver.satisfiable():
                    continue

            solver = claripy.Solver(backend=_MyBackendZ3())
            solver.add(cmp_expr)
            if not solver.satisfiable(extra_constraints=constraints):
                return True
        except Exception as e:
            # print('f1', f1)
            # print('f2', f2)
            # print('input1', input1)
            # print('input2', input2)
            # constraints = get_var_constraints(in1, input2[:min_num_var])
            # print('constraints')
            # for c in constraints:
            #     print(c)
            log.warning('Meet Z3 solver error %s' % str(e))
    return False


def ast_prove_f1_in_f2(f1, f2, c1=None, c2=None):
    # we merely prove the f1==f2 in the interval of join(c1, c2)
    input1 = get_expression_input(f1)
    input2 = get_expression_input(f2)
    if c1:
        for tmp in c1:
            input1.update(get_expression_input(tmp))
    if c2:
        for tmp in c2:
            input2.update(get_expression_input(tmp))
    input1 = list(input1)
    input2 = list(input2)

    print("f0:=%s\nf1:=%s\ninput0:=%s\ninput1:=%s\ncons0:=%s\ncons1:=%s" %
          (str(f1), str(f2), str(input1), str(input2), str(c1), str(c2)))
    print("%d / %d\n" % (len(input1), len(input2)))

    # we think f2 is always more complex than f1
    if len(input2) < len(input1):
        return False

    # compute the number of permutations
    permute_variables = len(input1)
    num_permutations = len(input2)
    for _i in range(len(input1)):
        num_permutations *= len(input2) - _i
    if len(input1) > 3 or num_permutations > 1000:
        # too many permutations, it wastes too much time
        # assigning same value to several input sources
        # merely permute the first 3 variables
        permute_variables = 3
    unsat_expr = claripy.ast.Bool(op='__ne__', args=(f1, f2))
    sat_expr = claripy.ast.Bool(op='__eq__', args=(f1, f2))
    ec2 = claripy.And(*[claripy.ast.Bool(op='__eq__', args=(claripy.Or(*c1), claripy.BoolV(True))),
                        claripy.ast.Bool(op='__eq__', args=(claripy.Or(*c2), claripy.BoolV(True)))])

    for in2 in permutations(input2, permute_variables):
        ec1 = []
        try:
            solver = claripy.Solver(backend=_MyBackendZ3())
            # symbolic input constraints
            for idx in range(len(in2)):
                ec1.append(claripy.ast.Bool(op='__eq__', args=(input1[idx], in2[idx])))
            ec1 = claripy.And(*ec1)
            solver.add(ec2)
            solver.add(ec1)
            if permute_variables == len(input1):
                # we do not need to concrete symbolic values here
                if solver.satisfiable(extra_constraints=[sat_expr]):
                    solver.add(unsat_expr)
                    if not solver.satisfiable():
                        return True
            else:
                # permute_variables < len(input1), we concrete all other variables of f1 and f2 to same value
                for concrete_value in [0, 1, 0xffffff]:
                    ec3 = []
                    for i in range(permute_variables, len(input1)):
                        ec3.append(input1[i] == concrete_value)
                    in2_var_names = set([var._encoded_name for var in in2])
                    for i in range(len(input2)):
                        if input2[i]._encoded_name not in in2_var_names:
                            ec3.append(input2[i] == concrete_value)
                    ec3 = claripy.And(*ec3)
                    # finally solve here repeatedly
                    if solver.satisfiable(extra_constraints=[sat_expr, ec3]):
                        if not solver.satisfiable([unsat_expr, ec3]):
                            return True
        except Exception as e:
            log.warning('Meet Z3 solver error %s' % str(e))
    return False


def ast_prove_f1_equi_f2(f1, f2, ptr_size1, ptr_size2, cmp_limit=720, equal_var=True):
    log.debug('ast_prove_f1_equi_f2')
    f1_in1, f2_in2 = check_and_return_formula_pair_with_inputs(f1, f2, ptr_size1, ptr_size2)
    if f1_in1 is None or f2_in2 is None:
        log.debug('inputs variables do not match')
        return False
    f1, input1 = f1_in1
    f2, input2 = f2_in2
    ne_f1_f2 = ne_formulas(f1, f2)
    if ne_f1_f2 is None:
        log.debug("fail2 to create not_equal formula")
        log.debug(f1)
        log.debug(f2)
        return False
    log.debug(f"To prove {str(ne_f1_f2)} UNSAT")

    solver = claripy.Solver(backend=_MyBackendZ3())
    solver.add(ne_f1_f2)
    count = 0
    for in2 in permutations(input2):
        count += 1
        if count > cmp_limit:
            raise TooManyVariables4Comparison(f1, f2, cmp_limit)
        try:
            ec1 = get_var_constraints(input1, in2)
            if ec1 is None:
                continue
            ec1 = claripy.And(*ec1)
            if not solver.satisfiable(extra_constraints=(ec1,)):
                return True
        except Exception as e:
            log.warning('Meet Z3 solver error %s' % str(e))
    return False

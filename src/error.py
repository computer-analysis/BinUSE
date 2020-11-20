"""
All exceptions
"""


class InvalidFunctionException(Exception):

    def __init__(self, func_addr: int):
        self._addr = func_addr

    def get_func_ptr(self):
        return self._addr

    def __str__(self):
        return 'Function 0x%x is not valid!' % self._addr

    def __repr__(self):
        return str(self)


class InvalidLipException(Exception):

    def __init__(self, lip, fail_block_id):
        self._lip = lip
        self._fail_block = fail_block_id

    def __str__(self):
        return str(self._lip) + ' is invalid. Angr cannot find block 0x%x(%d)' % (self._fail_block, self._fail_block)

    def __repr__(self):
        return str(self)


class TooHardToSolveException(Exception):
    def __init__(self, func_addr, num_scfg_nodes):
        self._func_addr = func_addr
        self._num_nodes = num_scfg_nodes

    def get_func_ptr(self):
        return self._func_addr

    def __str__(self):
        return "Function 0x%x is too hard to solve by angr, with %d nodes" % (self._func_addr, self._num_nodes)

    def __repr__(self):
        return str(self)


class TimeoutForCollectingInfoException(Exception):
    def __init__(self, block_id):
        self.block_id = block_id

    def __str__(self):
        return "Timeout for collecting info from " + str(self.block_id)

    def __repr__(self):
        return str(self)


class TimeoutForSMTSolver(Exception):

    def __str__(self):
        return "Timeout for SMT solver"

    def __repr__(self):
        return str(self)


class TooManyVariables4Comparison(Exception):

    def __init__(self, f1, f2, upper_bound):
        self.f1 = f1
        self.f2 = f2
        self.upper_bound = upper_bound

    def __str__(self):
        return "Too many variables to permute. %s and %s reach the upper bound %d" % \
               (str(self.f1), str(self.f2), self.upper_bound)

    def __repr__(self):
        return str(self)

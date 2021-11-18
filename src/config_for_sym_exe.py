import claripy
import angr


INIT_SP_VALUE_64 = 0x7fffffffffefff8
INIT_SP_VALUE_32 = 0x7ffeff6c


AMD64_init_rsp = claripy.BVV(INIT_SP_VALUE_64, 64)
X86_init_esp = claripy.BVV(INIT_SP_VALUE_32, 32)
AARCH64_init_sp = claripy.BVV(INIT_SP_VALUE_64, 64)

MIN_SP_VALUE_64 = 0x7fffffffffe0000
MAX_SP_VALUE_64 = 0x7ffffffffffffff

MIN_SP_VALUE_32 = 0x7ffe0000
MAX_SP_VALUE_32 = 0x7fffffff

_init_stack_pointer = {
    'AMD64': AMD64_init_rsp,
    'X86': X86_init_esp,
    'AARCH64': AARCH64_init_sp
}


def get_init_sp(p: angr.Project):
    return _init_stack_pointer[p.arch.name]


def init_state_sp(state: angr.SimState):
    p = state.project
    state.regs.sp = get_init_sp(p)

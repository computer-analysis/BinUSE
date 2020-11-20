from src.utils import *


def _call_root(block):
    last_instr = get_block_last_insn(block)
    return is_call_instr(last_instr)


def _ret_root(block):
    last_instr = get_block_last_insn(block)
    return is_ret_instr(last_instr)


def _conditional_jump_root(block):
    last_instr = get_block_last_insn(block)
    return is_conditional_jump(last_instr)


root_identify_table = [
    _call_root,
    _ret_root,
]


def ends_with_root_instr(block):
    for root_recognizer in root_identify_table:
        if root_recognizer(block):
            return True
    return False

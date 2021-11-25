"""
This file records the location of lib call arguments.
In most situations, for lib call of x64 binaries, we use registers rdi and rsi directly.
However, with different optimization options, the compiler may select different interfaces and the meaningful
arguments will be in other locations.
"""

X64_CALL_ARGUMENTS_MAP = {
    '.fprintf': {'rdi', 'rsi'},
    '.__fprintf_chk': {'rdi', 'rsi', 'rdx'},
    '.printf': {'rdi', 'rsi'},
    '.__printf_chk': {'rdi', 'rsi', 'rdx'},
    '.gettext': {'rdi'},
    '.dcgettext': {'rdi', 'rsi', 'rdx'},
    '.malloc': {'rdi'},
    '.fwrite': {'rdi', 'rsi', 'rdx', 'rcx'},
    '.__errno_location': None,
    '.abort': None,
    '.localeconv': None
}

X86_CALL_ARGUMENTS_MAP = {
    '.malloc': [4],
    '.gettext': [4],
    '.dcgettext': [4, 8, 12],
    '.fwrite': [4, 8, 12, 16],
    '.__errno_location': None,
    '.abort': None,
    '.localeconv': None,
    '.__assert_fail': [4, 8]
}

AARCH64_CALL_ARGUMENTS_MAP = {
    '.fprintf': {'x0', 'x1'},
    '.__fprintf_chk': {'x0', 'x1', 'x2'},
    '.printf': {'x0', 'x1'},
    '.__printf_chk': {'x0', 'x1', 'x2'},
    '.gettext': {'x0'},
    '.dcgettext': {'x0', 'x1', 'x2'},
    '.malloc': {'x0'},
    '.fwrite': {'x0', 'x1', 'x2', 'x3'},
    '.__errno_location': None,
    '.abort': None,
    '.localeconv': None
}

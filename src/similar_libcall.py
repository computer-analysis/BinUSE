"""
This file stores all lib calls which works in similar way
"""

_SIM_LIB_CALLS = [
    ['.gettext', '.dgettext', '.dcgettext'],
    ['.printf', '.__printf_chk'],
    ['.fprintf', '.__fprintf_chk'],
    ['.snprintf', '.__snprintf_chk'],
    ['.sprintf', '.__sprintf_chk'],
    ['.strcpy', '.__strcpy_chk'],
    ['.asprintf', '.__asprintf_chk'],
    # ['.strcmp', '.bsearch'],
    ['.toupper', '.__ctype_toupper_loc'],
    ['.tolower', '.__ctype_tolower_loc'],
    ['.siglongjmp', '.__longjmp_chk'],
    ['.fseeko', '.fseeko64'],
    ['.lseek', '.lseek64'],
    ['.open', '.open64'],
    ['.__libc_start_main', '__libc_start_main'],
    ['.__cxa_finalize', '__cxa_finalize'],
    ['.__xstat64', '.__xstat'],
    ['.realpath', '.__realpath_chk'],
]

_SIM_LIB_CALL_GROUPS = [
    [('.malloc', '.memset'), ('.calloc',)]
]

# these lib calls are likely inlined by compiler
_LIB_CALL_LOW_WEIGHT = [
    '.strcmp', 'strcmp', '.strncmp', '.bsearch'
    '.strcpy', 'strcpy',
    '.getc_unlocked',
    '.__uflow',  # this is a C-built-in function which is called merely with optimization
    '.free',
    '.ferror_unlocked'
]


def get_sim_lib_call_dict():
    res = dict()
    for funcs in _SIM_LIB_CALLS:
        for f in funcs:
            res[f] = funcs
    return res


SIM_LIB_CALL_DICT = get_sim_lib_call_dict()


def get_func_names_with_similar_libcall_replacement(funcs):
    res = []
    for f in funcs:
        if not f.startswith('.'):
            f = f".{f}"
        if f not in SIM_LIB_CALL_DICT.keys():
            res.append(f)
        else:
            res.append(SIM_LIB_CALL_DICT[f][0])
    res = set(res)
    # set the single similar functions first
    for fgs in _SIM_LIB_CALL_GROUPS:
        for fgroup in fgs:
            group_matched = 0
            for f in fgroup:
                if f in funcs:
                    group_matched += 1
                else:
                    break
            if group_matched == len(fgroup):
                # the whole lib call group exists in the list, replace it with the first functions group
                # discard original elements first
                for f in fgroup:
                    res.discard(f)
                res.update(set(fgs[0]))
                break
    # discard lib calls with few weights
    for f in _LIB_CALL_LOW_WEIGHT:
        res.discard(f)
    return res

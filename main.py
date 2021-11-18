import sys

from src.detector import *

logging.getLogger('angr').setLevel('ERROR')
log.setLevel('ERROR')

if __name__ == '__main__':
    p = load_proj(sys.argv[1], False)
    # cfg = p.analyses.CFGFast()

    p1 = load_proj(sys.argv[2], False)
    # cfg1 = p1.analyses.CFGFast()

    progress_outfile = None
    if len(sys.argv) > 3:
        progress_outfile = sys.argv[3]

    d = Detector(p, p1, mode='smt', alg='inline')
    load_fail = d.load_analysis()

    start = time.time()

    res = d.cmp_bins(mode='ri', progress_outfile=progress_outfile, not_sym_exe=False, no_skip=False)
    d.analyse_cmp_bins_res(res)
    d.save_to_disk(load_fail)

    print('elapse: %f' % (time.time() - start))


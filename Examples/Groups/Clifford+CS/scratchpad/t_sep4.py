import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import hybsep2 as H
from gadgetlib import Gad
bad = 0; good = 0
for (z, c, w) in ((2, 3, 1), (3, 1, 2), (1, 3, 2)):
    T = H.Tof(z, c, w)
    for tg in range(4):
        if tg == c: continue
        others = [x for x in range(4) if x not in (tg, c)]
        for mask in range(4):
            W = [c] + [others[i] for i in range(2) if mask >> i & 1]
            for dd in ((), ('K',), ('S', 'K')):
                for e in (1, -1):
                    g = Gad(tg, W, dd, e)
                    try:
                        H.tof_gadget_pass(T, g); good += 1
                    except Exception as ex:
                        bad += 1
                        if bad < 8: print('FAIL', T, g, repr(ex)[:400])
print('good', good, 'bad', bad)

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import hybsep2 as H
from gadgetlib import Gad
from t_lf import SQRT_V, SQRT_VI
for wv in (SQRT_VI, SQRT_V, 'SSKS'):
    print(wv, H.find_comm(wv))
bad = 0; good = 0
for wv in (SQRT_VI, SQRT_V, 'SSKS'):
    for (c, x, t) in ((3, 1, 0), (3, 2, 0), (1, 2, 0)):
        Q = H.Bar(wv, c, x, t)
        for tg in range(4):
            if tg == c: continue
            others = [w for w in range(4) if w not in (tg, c)]
            for mask in range(4):
                W = [c] + [others[i] for i in range(2) if mask >> i & 1]
                for dd in ((), ('K',), ('S', 'K')):
                    for e in (1, -1):
                        g = Gad(tg, W, dd, e)
                        try:
                            H.gadget_pass(Q, g); good += 1
                        except Exception as ex:
                            bad += 1
                            if bad < 8: print('FAIL', Q, g, repr(ex)[:300])
print('good', good, 'bad', bad)

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import hybsep2 as H
from deriv import BY_NAME
from t_lf import SQRT_V, SQRT_VI
c, x, t = 3, 1, 0
for wv in (SQRT_VI, SQRT_V, 'SSKS'):
    for (c, x, t) in ((3, 1, 0), (3, 2, 0), (1, 2, 0)):
        Q = H.Bar(wv, c, x, t)
        u = ({0,1,2,3} - {c,x,t}).pop()
        for (y, v) in ((t, u), (u, t), (x, u), (u, x), (x, t), (t, x)):
            try:
                n = H.wtof_pass(Q, y, v)
                print('ok', Q, 'Toff', y, 'not', c, v, len(BY_NAME[n].steps) if n in BY_NAME else '')
            except Exception as e:
                print('FAIL', Q, y, v, repr(e)[:300])

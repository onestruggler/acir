import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show
import facts4 as F
from dec import Dec
from hybtop import frame_top
D = Dec(4)
KIND = {('pp', False): 'p', ('pp', True): "p'", ('rot', False): 'l', ('rot', True): 'h', ('ki', False): 'k'}
def blocks(keys): return [F.decoded(a, KIND[(kind, fl)]) for (kind, a, fl) in keys]
def yb(j, k, l, m, s):
    K = lambda a, b: D.ki(a, b, s)
    lhs = K(j, k) + K(l, m) + K(j, l) + K(k, m)
    rhs = K(j, l) + K(k, m) + K(j, k) + K(l, m)
    return lhs, rhs
ops = frame_top()
for inst in [(12, 13, 14, 15, 11), (12, 14, 13, 15, 11), (8, 9, 10, 11, 7), (0, 1, 2, 3, 4)]:
    lk, rk = yb(*inst)
    L_, R_ = F.TF(ops, blocks(lk)), F.TF(ops, blocks(rk))
    lw, rw = norm(F.flat(L_)), norm(F.flat(R_))
    print(inst, 'gadgets', len(lk), len(rk), 'letters', len(lw), len(rw), 'valid', fp(lw) == fp(rw))

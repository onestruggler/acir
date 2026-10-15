# The new top-pair fact for ki-sq at n = 4: check its forms numerically.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show, inv
import facts4 as F
import hybtop as T

ops = T.frame_top()
def blk(a, kind): return norm(F.flatB(F.TF(ops, [F.decoded(a, kind)])[0]))
k = blk(14, 'k'); q13 = blk(13, "p'"); q14 = blk(14, "p'"); p14 = blk(14, 'p')
z = q13 + q13 + q14
E = fp([])
print('k^3 = e          ', fp(k + k + k) == E)
print('(k q13)^2 z = e  ', fp(k + q13 + k + q13 + z) == E)
print('q13 k q13^-1 = k^2 p14', fp(q13 + k + norm(inv(q13))) == fp(k + k + p14))
print('q13 k q13^-1 = k^2 q14', fp(q13 + k + norm(inv(q13))) == fp(k + k + q14))
print('len k', len(k), 'q13', len(q13), show(q13))

import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import samepair as SP
from samepair import mat, qof, _mm, _inv2, close
X = mat(['K', 'S', 'S', 'Kd'])
V = list('SSKS')
k0 = _mm(_mm(mat(V + V), mat(['K'])), _mm(_inv2(mat(V + V)), mat(['Kd'])))
kk = _mm(_mm(X, k0), X)
lets = {'p': qof([], 1), 'q': _mm(_mm(X, qof([], 1)), X), 'l': qof(['S', 'K'], -1), 'h': _mm(_mm(X, qof(['S', 'K'], -1)), X)}
def prodw(w):
    R = ((1, 0), (0, 1))
    for x in w: R = _mm(R, lets[x])
    return R
for name in ('p', 'l'):
    target = _mm(_mm(kk, lets[name]), _inv2(kk))
    for n in range(1, 4):
        ws = [w for w in itertools.product(lets, repeat=n) if close(prodw(w), target)]
        if ws: print(name, '->', ws[:6]); break
# k^3
k3 = _mm(_mm(kk, kk), kk); print('k^3 = I:', close(k3, ((1, 0), (0, 1))))

import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import facts4 as F
from deriv import expand, norm, show
from prover2 import apply, P, DIM
from t_shift2 import best
A, B, Hc, Hc1 = [norm(F.flatB(b)) for b in best[2]]
def mat(word):
    cols = []
    for j in range(DIM):
        v = [1 if i == j else 0 for i in range(DIM)]
        for op in reversed(expand(word)): v = apply(op, v)
        cols.append(v)
    return [[cols[j][i] for j in range(DIM)] for i in range(DIM)]
def mm(X, Y): return [[sum(X[i][k] * Y[k][j] for k in range(DIM)) % P for j in range(DIM)] for i in range(DIM)]
MA, MB, MH, MH1 = mat(A), mat(B), mat(Hc), mat(Hc1)
Y = mm(MA, MB)
print('Y H = H1 Y:', mm(Y, MH) == mm(MH1, Y))
# Y on the block x2 = x3 = 1, identity elsewhere?
blk = [x for x in range(DIM) if (x >> 2) & 1 and (x >> 3) & 1]
off = all(Y[i][j] == (1 if i == j else 0) for i in range(DIM) for j in range(DIM) if i not in blk or j not in blk)
print('Y trivial off the block:', off)
F4 = [[Y[i][j] for j in blk] for i in blk]
for r in F4: print(r)

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import facts4 as F
import hyb_classes as HC
from t_shiftcls import sem
from deriv import fp, norm, show
G = F.group()
c = 0
blocks = [F.decoded(c, 'l'), F.decoded(c + 1, 'l'), F.decoded(c, 'k'), F.decoded(c + 1, 'k')]
best = None
for ops in G:
    bt = F.TF(ops, blocks)
    s = [sem(b) for b in bt]
    tA, tB = s[0][2], s[1][2]
    tH, tH1 = s[2][2][0], s[3][2][0]
    if (tA, tB, tH, tH1) == (0, 1, 0, 1):
        key = tuple(s)
        if best is None or key < best[0]: best = (key, ops, bt)
for b in best[0]: print(b)
print(best[1])

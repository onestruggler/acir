import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import facts4 as F, hyb_classes as HC
from dec import code
from hybtop import frame_top
ops = frame_top()
print('frame', ops)
for c in range(11, 15):
    for kind in ('k', 'l', 'p'):
        b = F.TF(ops, [F.decoded(c, kind)])[0]
        print(c, kind, b[0], HC.hyb_roles(b[1]) if kind == 'k' else F.sem(b))
for c in range(11, 16): print(c, code(4, c))

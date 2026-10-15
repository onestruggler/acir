import sys, os, traceback
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import hybsep3 as H3
from hybsep2 import Bar
from t_lf import SQRT_V, SQRT_VI
from deriv import norm, show
from dec import barenco
# black Bar(SSKSKK; 2,3 -> 0) against a white piece: X2 X3? reproduce KeyError on a white Barenco with Kd root
Q = Bar(SQRT_VI, 2, 3, 0)
R = norm([('X', 2)] + barenco(list('S') + ['Kd'], 2, 1, 0) + [('X', 2)])
try:
    print(H3.piece_piece(Q, R))
except Exception: traceback.print_exc()

# Barenco's three-control decomposition of the hybrid.  The decoded hybrid
# [Bar(V; 1,2 -> 0), CK(3 -> 0)] is L_123(V^-2) (kappa = V^-2: K inverts V),
# and pulling control 1 out of Barenco's lemma gives
#     Lambda_1(Bar(V^-1; 2,3 -> 0)) = L_12(V^-1) Toff(3;1,2) L_13(V) Toff(3;1,2) L_13(V^-1),
# where L_1x(V^a) is Barenco's word for a square root of V^a (controls 1, x).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show
from dec import G_ki, barenco

SQRT_V, SQRT_VI = 'SSSKSS', 'SSKSKK'          # square roots of V and V^-1 in <S, K>

def L2(c, x, t, a):
    """the doubly controlled V^a (a = +-1) on t, controls c, x: Barenco's word."""
    return norm(barenco(SQRT_V if a == 1 else SQRT_VI, c, x, t))

def LF(c=1, w=2, z=3, t=0):
    return (L2(c, w, t, -1) + [('TOFF', z, c, w)] + L2(c, z, t, 1)
            + [('TOFF', z, c, w)] + L2(c, z, t, -1))

HD = norm(G_ki(4))

if __name__ == '__main__':
    lf = norm(LF())
    print('decoded hybrid', len(HD), 'letters; decomposition', len(lf), 'letters')
    print('equal:', fp(HD) == fp(lf))

# Experiment: does the passes engine find that a unit controlled white by
# c passes the hybrid core L_{123}(kappa_0) = [Bar(V^2; 1,2 -> 0), CK(3 -> 0)]?
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import norm, fp, show
import passes as P
from passes import L
import gadgetlib as G
from dec import G_ki

KI = norm(G_ki(4))
print('KI core', len(KI), show(KI))
for c in (1, 2, 3):
    for x in ('K', 'S'):
        U = [G.nc_unit(c, 0, x)]
        try:
            n = P.prove(U, P.units(KI))
            print('OK', c, x, n)
        except P.Fail as e:
            print('FAIL', c, x, str(e)[:300])

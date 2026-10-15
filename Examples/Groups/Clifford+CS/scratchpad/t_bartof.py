# The candidate fourth rule bar-tof: Barenco's L_12(V^2) on target 0 (black
# on wire 1) commutes with the Toffoli on target 0 controlled by wire 1
# white and wire 3.  Sound?  Derivable by the passes engine?
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show
import passes as P
from dec import barenco
BAR = norm(barenco('SSKS', 1, 2, 0))
TW = [('X', 1), ('TOFF', 0, 1, 3), ('X', 1)]
print('Bar', len(BAR), show(BAR))
print('sound:', fp(BAR + TW) == fp(TW + BAR))
try:
    n = P.prove([tuple(BAR)], [tuple(TW)])
    print('DERIVABLE', n)
except P.Fail as e:
    print('engine: no derivation', str(e)[:200])

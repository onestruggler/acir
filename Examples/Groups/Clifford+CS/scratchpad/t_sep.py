# Experiment: can the passes engine show that the pieces of Barenco's
# three-control decomposition (t_lf.LF, black on the separator c) pass a
# white-c phase gadget, class (b) of hyb_classes?
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show
import passes as P
from gadgetlib import Gad
from t_lf import L2, LF

def pieces(c, w, z, t):
    return [L2(c, w, t, -1), [('TOFF', z, c, w)], L2(c, z, t, 1), [('TOFF', z, c, w)], L2(c, z, t, -1)]

def tryit(c, w, z, t, g):
    gl = g.letters()
    for k, pc in enumerate(pieces(c, w, z, t)):
        ok = fp(norm(pc) + gl) == fp(gl + norm(pc))
        try:
            n = P.prove([tuple(norm(pc))], [tuple(gl)])
            print(k, 'ok', show(pc)[:60], '|', n[:60])
        except P.Fail as e:
            print(k, 'FAIL (sem %s)' % ok, show(pc)[:60], '|', str(e)[:300])
        try:
            n = P.prove(P.units(norm(pc)), [tuple(gl)])
            print('   letterwise ok')
        except P.Fail as e:
            print('   letterwise FAIL', str(e)[:300])

if __name__ == '__main__':
    # class (b): hybrid t 0, single 2, pair {1,3}; PP target 1 white on 3
    tryit(3, 1, 2, 0, Gad(1, (3,)))

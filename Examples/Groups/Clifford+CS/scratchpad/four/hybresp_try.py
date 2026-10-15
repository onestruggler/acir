import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import BY_NAME, DERIVATIONS
import hybplan as HP
import hybshift as HS
import facts4 as F
out, missing = HP.plan()
need = set()
for (inst, ops, fn, kl, kr, sw, rs) in out:
    for p in rs:
        if len(p[0]) == len(F.KIMID): need.add(p)
n0 = len(DERIVATIONS); t = time.time(); tot = 0
for a, b in sorted(need):
    nm = HS.respell_hyb(a, b)
    tot += len(BY_NAME[nm].steps)
print('respellings', len(need), 'top-level steps', tot, 'new derivations', len(DERIVATIONS) - n0, 'secs', int(time.time() - t))
for d in DERIVATIONS[n0:]:
    print('  ', d.name[:70], len(d.steps))

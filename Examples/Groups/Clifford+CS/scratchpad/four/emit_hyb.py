# emit.py's run, with the hybrid's derivations after the K-free facts.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.environ.setdefault('DERIV_QUIET', '1')
import deriv
import lower as LW
import emit
import lib4, consec4
consec4.all_facts()
import table
table.make()
import facts4
facts4.make_all()
n0 = len(deriv.DERIVATIONS)
import hybfar, hybsym, hybshift, hybtop
names = hybfar.make_all() + [hybsym.sym()] + hybshift.make_all() + hybtop.make_all() + [hybtop.bridge_gki()]
# the respellings the four-wire instances of the hybrid facts need (hybplan)
import hybplan
plan, missing = hybplan.plan()
assert not missing, missing
for (inst, ops, fn, kl, kr, sw, rs) in plan:
    for (a, b) in rs:
        if len(a) == len(facts4.KIMID): names.append(hybshift.respell_hyb(a, b))
        else: assert facts4.respell(a) is not None
# rules hyb-sq and hyb-yb at the top frame
names.append(hybtop.C_sq())
import gen_yb
names.append(gen_yb.C_yb())
print('hybrid facts:', len(names), 'new derivations:', len(deriv.DERIVATIONS) - n0, flush=True)
prims = LW.lower_all(deriv.DERIVATIONS)
print('lowered', len(prims), sum(len(p.steps) for p in prims), flush=True)
mods = emit.write_all(prims)
print(len(mods), 'modules written')

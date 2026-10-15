# Run the joint paper's five-wire derivations (joint/run_all.py, and with
# --deb the de-borrowing ones of joint/deb_all.py) recording each step's
# replacement segment, and pickle them for the lowering (lower5.py).
#   python3 load5.py OUT.pkl [--deb]
import sys, os, io, contextlib, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
JD = os.path.join(os.path.dirname(HERE), 'joint')
sys.path.insert(0, JD); os.chdir(JD)
import derivn
_orig = derivn.Derivation._set
def _set(self, new, kind, info, k, n):
    seg = list(new[k:k + len(new) - len(self.cur) + n])
    _orig(self, new, kind, info, k, n)
    self.steps[-1] = self.steps[-1] + (seg,)
derivn.Derivation._set = _set
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    import run_all
    if '--deb' in sys.argv:
        sys.argv = ['run_all.py', '--dump']
        import importlib; importlib.reload(run_all)
        import runpy
        runpy.run_path('deb_all.py', run_name='deb_all')
from derivn import DERIVATIONS
from w5lib import L
out = {'derivs': [dict(name=d.name, lhs=d.lhs, rhs=d.rhs, steps=d.steps) for d in DERIVATIONS],
       'L': dict(L)}
pickle.dump(out, open(sys.argv[1], 'wb'))
print(len(out['derivs']), 'derivations,', sum(len(d['steps']) for d in out['derivs']), 'steps')

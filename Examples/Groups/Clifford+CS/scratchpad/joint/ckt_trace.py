# ckt.py with progress: lemma completions printed, a stack dump every ten
# minutes (to find where the derivation spends its time).
import faulthandler, sys, time
faulthandler.dump_traceback_later(600, repeat=True)
import derivn
T0 = time.time()
_done = derivn.Derivation.done
def done(self):
    r = _done(self)
    if self.name.startswith(('ckt', 'nf-ckt', 'F1-ck', 'S2-', 'L-')):
        print(f'[{time.time() - T0:7.0f}s] ok {self.name}: {len(self.steps)} steps', flush=True)
    return r
derivn.Derivation.done = done
import box, f5, boxsym, boxdash, boxbox, f0, f4, f4cs, boxtoff, boxck, ssym, f1
def timed(mod, fname):
    f = getattr(mod, fname)
    def g(*a, **k):
        t = time.time(); r = f(*a, **k)
        print(f'[{time.time() - T0:7.0f}s] {mod.__name__}.{fname} ({time.time() - t:.0f}s)', flush=True)
        return r
    setattr(mod, fname, g)
for mod in (box, f5, boxsym, boxdash, boxbox, f0, f4, f4cs, boxtoff, boxck, ssym):
    timed(mod, 'build')
timed(boxsym, 'build_perms')
timed(f1, 'nf')
sys.argv = ['ckt.py']
import runpy
print(f'[{time.time() - T0:7.0f}s] start', flush=True)
runpy.run_path('ckt.py', run_name='__main__')
print(f'[{time.time() - T0:7.0f}s] finished', flush=True)

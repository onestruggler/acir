"""Helpers for developing the runs of Sec8/D/N8 in the model se.py.

Letters as in se.py.  `R` builds a run step by step, finding the wire of each
semantic step automatically, and prints it in Lean syntax.
"""
import sys
sys.path.insert(0, '.')
from se import *

T_ = True; F_ = False

def tau(j, q): return j + 1 if q == j else (j if q == j + 1 else q)

def swapG(j, x):
    _, Kd, tg, cs, b = x
    return ('g', Kd, tuple(tau(j, t) for t in tg), tuple((tau(j, p), v) for p, v in cs), b)

def H_(j): return S('H', j)
def Z_(j): return S('Z', j)
def C_(j): return S('C', j)
def K_(j): return S('K', j)
def SW(j): return S('S', j)

def sw(j, x): return ([SW(j), x, SW(j)], [swapG(j, x)])

def ppL(i):
    return [K_(i), H_(i + 1), Z_(i), K_(i), H_(i + 1), Z_(i), K_(i), H_(i + 1), Z_(i), SW(i)]

def X_(j): return [H_(j), Z_(j), H_(j)]

class Run:
    def __init__(self, k, T, w, name=''):
        self.k = k; self.T = T; self.cur = list(w); self.steps = []; self.name = name
        self.ok = True
    def _do(self, st):
        if not self.ok: return self
        nxt = apply(self.k, self.T, self.cur, st)
        if nxt is None:
            print('FAILED', self.name, 'at step', len(self.steps), st)
            print('   cur =', self.cur)
            self.ok = False
            return self
        self.steps.append(st); self.cur = nxt
        return self
    def rw(self, i, e, d=False): return self._do(('rw', i, e, d))
    def swp(self, i): return self._do(('sw', i))
    def sem(self, i, ln, r, q=None):
        if not self.ok: return self
        win = self.cur[i:i + ln]
        if q is None:
            qs = [q for q in range(self.k + 1) if semOK(self.k, q, win, list(r))]
            if not qs:
                print('FAILED', self.name, 'sem at step', len(self.steps), (i, ln))
                print('   win =', win); print('   r   =', list(r))
                self.ok = False
                return self
            q = qs[-1]
        return self._do(('sem', i, ln, list(r), q))
    def expect(self, v):
        if self.ok and self.cur != list(v):
            print('MISMATCH', self.name); print('   cur =', self.cur); print('   exp =', list(v))
            self.ok = False
        elif self.ok:
            print('ok', self.name, len(self.steps), 'steps')
        return self

def eqsem(K, l, r, Ns=(5, 6)):
    """l = r numerically at the given widths (bulk above K)."""
    return all(eqm(N, wc(K, N, l), wc(K, N, r)) for N in Ns)

# ---- Lean printing ----
def lean_letter(x, names):
    if x in names: return names[x]
    if x[0] == 's':
        return '.s (.%s %d)' % (x[1], x[2])
    _, Kd, tg, cs, b = x
    return '.g .%s [%s] [%s] %s' % (Kd, ', '.join(map(str, tg)),
        ', '.join('(%d, %s)' % (p, 'true' if v else 'false') for p, v in cs), 'true' if b else 'false')

def lean_word(w, names):
    return '[' + ', '.join(lean_letter(x, names) for x in w) + ']'

def lean_steps(steps, names):
    out = []
    for st in steps:
        if st[0] == 'rw': out.append('.rw %d %d %s' % (st[1], st[2], 'true' if st[3] else 'false'))
        elif st[0] == 'sw': out.append('.sw %d' % st[1])
        else: out.append('.sem %d %d %s %d' % (st[1], st[2], lean_word(st[3], names), st[4]))
    return out

# ---- the fixed-width equations of SmallDefs.lean as letter words ----
import re as _re, os as _os
def small_eqs(path=None):
    path = path or _os.path.join(_os.path.dirname(_os.path.abspath(__file__)),
                                 '../../Sec8/D/SmallDefs.lean')
    txt = open(path).read()
    out = {}
    for m in _re.finditer(r'def ([lr])(\d+[ab]?) : Circ (\d+) :=\s*circW \d+ \(\[(.*?)\]\)', txt, _re.S):
        side, num, K, body = m.group(1), m.group(2), int(m.group(3)), m.group(4)
        lets = [('s', k, int(j)) for k, j in _re.findall(r'L\.([HZCKS]) (\d+)', body)]
        out.setdefault(num, [K, None, None])
        out[num][1 if side == 'l' else 2] = lets
    return out

# ---- runs of the fixed-width engine WEng (tokens of gen/sec8/w4/tok.py) ----
def _tok():
    import sys as _s
    p = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'w4')
    if p not in _s.path:
        _s.path.insert(0, p)
    import tok
    return tok

class WRun:
    """A WEng run on M + 1 wires (tokens of tok.py: ('s', k, j), ('g', Kd, tg, cs), ('p', m, w, ps))."""
    def __init__(self, M, T, w, name=''):
        self.tok = _tok(); self.M = M; self.T = T; self.cur = list(w); self.steps = []
        self.name = name; self.ok = True
        self.eng = self.tok.Engine(M, T)
    def _do(self, st):
        if not self.ok: return self
        nxt = self.eng.apply_step(self.cur, st)
        if nxt is None:
            print('FAILED', self.name, 'at step', len(self.steps), st); print('   cur =', self.cur)
            self.ok = False; return self
        self.steps.append(st); self.cur = nxt; return self
    def rw(self, i, e, d=False): return self._do(('rw', i, e, d))
    def swp_(self, i): return self._do(('sw', i))
    def swp(self, i, j, a, b, d=False): return self._do(('swp', i, j, a, b, d))
    def sem(self, i, ln, r, q=None):
        if not self.ok: return self
        win = self.cur[i:i + ln]
        if q is None:
            qs = [q for q in range(self.M + 1) if self.tok.sem_ok(self.M, q, list(win), list(r))]
            if not qs:
                print('FAILED', self.name, 'sem at step', len(self.steps), (i, ln))
                print('   win =', win); print('   r   =', list(r)); self.ok = False; return self
            q = qs[0]
        return self._do(('sem', i, ln, tuple(r), q))
    def expect(self, v):
        if self.ok and self.cur != list(v):
            print('MISMATCH', self.name); print('   cur =', self.cur); print('   exp =', list(v)); self.ok = False
        elif self.ok: print('ok', self.name, len(self.steps), 'steps')
        return self

def wlean_tok(t, names):
    if t in names: return names[t]
    if t[0] == 's': return '.s (.%s %d)' % (t[1], t[2])
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return '.g .%s [%s] [%s]' % (Kd, ', '.join(map(str, tg)),
            ', '.join('(%d, %s)' % (w, 'true' if c else 'false') for w, c in cs))
    _, m, w, ps = t
    return '.p %d [%s] [%s]' % (m, ', '.join('.%s %d' % (l[0], l[1]) for l in w), ', '.join(map(str, ps)))

def wlean_word(w, names): return '[' + ', '.join(wlean_tok(t, names) for t in w) + ']'

def wlean_steps(steps, names):
    out = []
    for st in steps:
        if st[0] == 'rw': out.append('.rw %d %d %s' % (st[1], st[2], 'true' if st[3] else 'false'))
        elif st[0] == 'sw': out.append('.sw %d' % st[1])
        elif st[0] == 'swp':
            out.append('.swp %d %d (%s) (%s) %s' % (st[1], st[2], wlean_tok(st[3], names),
                       wlean_tok(st[4], names), 'true' if st[5] else 'false'))
        else: out.append('.sem %d %d %s %d' % (st[1], st[2], wlean_word(st[3], names), st[4]))
    return out

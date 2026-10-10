"""Forms and the route check, mirroring Check.agda / Forms.agda exactly.

Numbers are pairs (a, b) = a + b sqrt2.  A form is a constant and a dict
var -> coefficient.  Routes are lists of letters in application order:
('H', i, j), ('X', i, j), ('Z', i) on row names."""
from collections import Counter

ZERO = (0, 0); ONE = (1, 0); R2 = (0, 1)
def zadd(x, y): return (x[0] + y[0], x[1] + y[1])
def zsub(x, y): return (x[0] - y[0], x[1] - y[1])
def zneg(x): return (-x[0], -x[1])
def zmul(x, y): return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
def zhalf(x):  # x / sqrt2 when the rational part is even (halfZ)
    if x[0] & 1: return None
    return (x[1], x[0] // 2)

class F:
    __slots__ = ('c', 'v')
    def __init__(s, c=ZERO, v=None):
        s.c = c; s.v = {k: x for k, x in (v or {}).items() if x != ZERO}
    def __add__(s, o):
        v = dict(s.v)
        for k, x in o.v.items(): v[k] = zadd(v.get(k, ZERO), x)
        return F(zadd(s.c, o.c), v)
    def __neg__(s): return F(zneg(s.c), {k: zneg(x) for k, x in s.v.items()})
    def __sub__(s, o): return s + (-o)
    def scale(s, z): return F(zmul(s.c, z), {k: zmul(x, z) for k, x in s.v.items()})
    def half(s):
        c = zhalf(s.c)
        if c is None: return None
        v = {}
        for k, x in s.v.items():
            h = zhalf(x)
            if h is None: return None
            v[k] = h
        return F(c, v)
    def subst(s, env):
        out = F(s.c)
        for k, x in s.v.items():
            out = out + (env[k].scale(x) if k in env else F(ZERO, {k: x}))
        return out
    def key(s): return (s.c, tuple(sorted(s.v.items())))
    def __repr__(s):
        def z(x):
            a, b = x
            if b == 0: return str(a)
            if a == 0: return '%s√2' % b
            return '(%s%+d√2)' % (a, b)
        t = [z(s.c)] if s.c != ZERO else []
        for k in sorted(s.v): t.append('%s·%s' % (z(s.v[k]), k))
        return ' + '.join(t) or '0'

def const(a, b=0): return F((a, b))
def var(name, co=ONE): return F(ZERO, {name: co})

# --- parities (Forms.agda) ---
def evenV(f): return all(not (x[0] & 1) for x in f.v.values())
def twoV(f): return all(not (x[0] & 1) and not (x[1] & 1) for x in f.v.values())
def evenF(f): return not (f.c[0] & 1) and evenV(f)
def oddF(f): return bool(f.c[0] & 1) and evenV(f)
def clsF(f): return (f.c[1] & 1) if twoV(f) else None

# The split form deciding the parity of f, and the class of f.
def par_dep(f):
    us = sorted(k for k, x in f.v.items() if x[0] & 1)
    return us
def cls_dep(f):
    us = sorted(k for k, x in f.v.items() if x[1] & 1)
    return us

class Dep(Exception):
    def __init__(s, kind, us): s.kind = kind; s.us = tuple(us)

# --- check (Check.agda) ---
def stepF(g, fs):
    fs = dict(fs)
    if g[0] == 'H':
        i, j = g[1], g[2]
        a = (fs[i] + fs[j]).half(); b = (fs[i] - fs[j]).half()
        if a is None or b is None:
            for s in (fs[i] + fs[j], fs[i] - fs[j]):
                us = par_dep(s)
                if us: raise Dep('par', us)
            return None
        fs[i] = a; fs[j] = b
    elif g[0] == 'X':
        fs[g[1]], fs[g[2]] = fs[g[2]], fs[g[1]]
    else:
        fs[g[1]] = -fs[g[1]]
    return fs

def noddF(fs):
    c = 0
    for r in sorted(fs):
        f = fs[r]
        if oddF(f): c += 1
        elif evenF(f): pass
        else: raise Dep('par', par_dep(f))
    return c

def kindF(fs):
    c = noddF(fs)
    if c <= 3: return 'low'
    if c == 4: return 'atL'
    return None

def plainF(g, fs):
    if g[0] != 'H': return True
    a, b = fs[g[1]], fs[g[2]]
    if evenF(a) or evenF(b): return True
    for f in (a, b):
        if not oddF(f): raise Dep('par', par_dep(f))
    ca, cb = clsF(a), clsF(b)
    if ca is None: raise Dep('cls', cls_dep(a))
    if cb is None: raise Dep('cls', cls_dep(b))
    return ca == cb

def distinct(g): return g[0] == 'Z' or g[1] != g[2]

def check(route, fs):
    """True, False, or raises Dep (with .pos, the letters passed)."""
    try:
        return check_(route, fs)
    except Dep as d:
        d.pos = PROG[0]
        raise
PROG = [0]
def check_(route, fs):
    k = kindF(fs)
    for t, g in enumerate(route):
        PROG[0] = t
        fs2 = stepF(g, fs)
        if fs2 is None: return False
        if not distinct(g): return False
        k2 = kindF(fs2)
        if k == 'low' and k2 == 'low': ok = True
        elif k == 'atL' and k2 is not None: ok = plainF(g, fs)
        elif k == 'low' and k2 == 'atL': ok = plainF(g, fs2)
        else: ok = False
        if not ok: return False
        fs, k = fs2, k2
    return True

def run(route, fs):
    """the forms after a route (stepF only), or raises Dep / returns None"""
    for g in route:
        fs = stepF(g, fs)
        if fs is None: return None
    return fs

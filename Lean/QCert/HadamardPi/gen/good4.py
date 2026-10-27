# Symbolic numerators on a window of four odd entries of one class:
#   u_j = (2 a_j + 1) + (2 b_j + c) sqrt2,  a_0 + a_1 + a_2 + a_3 = 2 mm + par.
# For a word w (written order), the scaled action scw multiplies the H-pairs as
# (x + y, x - y) and every other entry by sqrt2; dividing by sqrt2^h gives the numerators at
# the old exponent, which must be integral linear forms after eliminating a_3.
from fractions import Fraction as F

VARS = ['a0', 'a1', 'a2', 'a3', 'b0', 'b1', 'b2', 'b3', 'c', 'mm', '1']

class Lin:
    def __init__(self, d=None):
        self.d = {k: F(v) for k, v in (d or {}).items() if v != 0}
    def __add__(s, o):
        d = dict(s.d)
        for k, v in o.d.items(): d[k] = d.get(k, 0) + v
        return Lin(d)
    def __neg__(s): return Lin({k: -v for k, v in s.d.items()})
    def __sub__(s, o): return s + (-o)
    def scale(s, r): return Lin({k: v * r for k, v in s.d.items()})
    def subst_a3(s, par):
        # a3 = 2 mm + par - a0 - a1 - a2
        d = dict(s.d)
        v = d.pop('a3', 0)
        out = Lin(d)
        if v:
            out = out + Lin({'mm': 2 * v, '1': par * v, 'a0': -v, 'a1': -v, 'a2': -v})
        return out
    def integral(s): return all(v.denominator == 1 for v in s.d.values())
    def even(s): return all(v.denominator == 1 and v.numerator % 2 == 0 for v in s.d.values())
    def lean(s):
        names = {'a0': 'a 0', 'a1': 'a 1', 'a2': 'a 2', 'a3': 'a 3', 'b0': 'b 0', 'b1': 'b 1',
                 'b2': 'b 2', 'b3': 'b 3', 'c': 'c', 'mm': 'mm'}
        terms = []
        for k in VARS:
            v = s.d.get(k, 0)
            if v == 0: continue
            assert v.denominator == 1
            v = v.numerator
            if k == '1':
                t = str(abs(v))
            else:
                t = names[k] if abs(v) == 1 else f"{abs(v)} * {names[k]}"
            terms.append((v < 0, t))
        if not terms: return "0"
        out = ("-" if terms[0][0] else "") + terms[0][1]
        for neg, t in terms[1:]:
            out += (" - " if neg else " + ") + t
        return out

class Q:
    """x + y sqrt2 with x, y linear forms"""
    def __init__(self, x, y): self.x, self.y = x, y
    def __add__(s, o): return Q(s.x + o.x, s.y + o.y)
    def __sub__(s, o): return Q(s.x - o.x, s.y - o.y)
    def __neg__(s): return Q(-s.x, -s.y)
    def rt2(s): return Q(s.y.scale(2), s.x)          # sqrt2 * (x + y sqrt2) = 2y + x sqrt2
    def div_rt2(s): return Q(s.y, s.x.scale(F(1, 2)))  # (x + y sqrt2)/sqrt2 = y + (x/2) sqrt2

def pattern():
    return [Q(Lin({f'a{j}': 2, '1': 1}), Lin({f'b{j}': 2, 'c': 1})) for j in range(4)]

def scg(l, U):
    U = list(U)
    if l[0] == 'Z':
        U[l[1]] = -U[l[1]]
    elif l[0] == 'X':
        p, q = l[1], l[2]
        U[p], U[q] = U[q], U[p]
    else:
        p, q = l[1], l[2]
        x, y = U[p], U[q]
        V = [U[i].rt2() for i in range(len(U))]
        V[p] = x + y; V[q] = x - y
        U = V
    return U

def scw(w, U):
    for l in reversed(w):
        U = scg(l, U)
    return U

def hcnt(w): return sum(1 for l in w if l[0] == 'H')

def numerators(w, par):
    U = scw(w, pattern())
    out = []
    for e in U:
        for _ in range(hcnt(w)):
            e = e.div_rt2()
        e = Q(e.x.subst_a3(par), e.y.subst_a3(par))
        if not (e.x.integral() and e.y.integral()):
            return None
        out.append(e)
    return out

def good(w, par):
    """(U', j) with U' the numerators and j an entry with identically even real part, or None."""
    U = numerators(w, par)
    if U is None: return None
    for j, e in enumerate(U):
        if e.x.even(): return U, j
    return U, None

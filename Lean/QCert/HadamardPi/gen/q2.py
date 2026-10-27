# Exact arithmetic in Q(sqrt2) and words of two-level matrices on m indices.
from fractions import Fraction as F
import itertools

class Q2:
    __slots__ = ("a", "b")
    def __init__(self, a, b=0):
        self.a = F(a); self.b = F(b)
    def __add__(s, o): return Q2(s.a + o.a, s.b + o.b)
    def __sub__(s, o): return Q2(s.a - o.a, s.b - o.b)
    def __neg__(s): return Q2(-s.a, -s.b)
    def __mul__(s, o): return Q2(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)
    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def __repr__(s): return f"({s.a}+{s.b}r2)"
    def integral(s): return s.a.denominator == 1 and s.b.denominator == 1
    def odd(s): return s.integral() and s.a.numerator % 2 != 0

S = Q2(0, F(1, 2))    # 1/sqrt2
ZERO = Q2(0); ONE = Q2(1)

# a letter: ('H', i, j) with i<j, ('X', i, j), ('Z', i)
def act(letter, v):
    v = list(v)
    if letter[0] == 'H':
        _, i, j = letter
        x, y = v[i], v[j]
        v[i] = S * (x + y); v[j] = S * (x - y)
    elif letter[0] == 'X':
        _, i, j = letter
        v[i], v[j] = v[j], v[i]
    else:
        _, i = letter
        v[i] = -v[i]
    return v

def run(word, v):
    # word in written order; rightmost acts first
    for l in reversed(word):
        v = act(l, v)
    return v

def states(word, v):
    out = [list(v)]
    for l in reversed(word):
        v = act(l, v)
        out.append(v)
    return out

def matrix(word, m):
    cols = []
    for c in range(m):
        e = [ONE if i == c else ZERO for i in range(m)]
        cols.append(tuple(run(word, e)))
    return tuple(cols)

# Exact Z[sqrt2] numerators: (x, y) = x + y sqrt2, integers.  Columns as lists at exponent k.
import random, itertools
from collections import deque
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def neg(a): return (-a[0], -a[1])
def rt2(a): return (2 * a[1], a[0])
def div_rt2(a):
    if a[0] % 2: return None
    return (a[1], a[0] // 2)
def odd(a): return a[0] % 2 != 0
def cls(a): return a[1] % 2
def depth(a):
    d = 0
    if a == (0, 0): return 99
    while not odd(a):
        a = div_rt2(a); d += 1
    return d
def lde_reduce(col, k):
    # reduce exponent while all even
    while k > 0 and all(not odd(e) for e in col):
        col = [div_rt2(e) for e in col]; k -= 1
    return col, k
def act(l, col):
    """letter on numerators at a fixed exponent: returns None if not integral"""
    col = list(col)
    if l[0] == 'Z': col[l[1]] = neg(col[l[1]]); return col
    if l[0] == 'X':
        p, q = l[1], l[2]; col[p], col[q] = col[q], col[p]; return col
    p, q = l[1], l[2]
    s = div_rt2(add(col[p], col[q])); d = div_rt2(sub(col[p], col[q]))
    if s is None or d is None: return None
    col[p] = s; col[q] = d
    return col
def act_raise(l, col, k):
    """letter with exponent bookkeeping (may raise k)"""
    c2 = act(l, col)
    if c2 is not None: return lde_reduce(c2, k)
    col = [rt2(e) for e in col]
    return lde_reduce(act(l, col), k + 1)
def random_column(n, steps, rng):
    col = [(0, 0)] * n; col[n - 1] = (1, 0); k = 0
    for _ in range(steps):
        r = rng.random()
        i, j = rng.sample(range(n), 2); i, j = min(i, j), max(i, j)
        if r < 0.6: l = ('H', i, j)
        elif r < 0.85: l = ('X', i, j)
        else: l = ('Z', i)
        col, k = act_raise(l, col, k)
    return col, k
def norm_ok(col, k):
    X = sum(a * a + 2 * b * b for a, b in col); Y = sum(a * b for a, b in col)
    return X == 2 ** k and Y == 0

"""Sides of any step family: Table 1 ('r1a'...), macros ('ksym4'...), and
their reversals ('rev_r4b', 'rev_ksym5')."""
from rules import sides as tsides
from macros import BASE, ren

def any_sides(fam, ps):
    rev = fam.startswith('rev_')
    f = fam[4:] if rev else fam
    if f in BASE:
        k, l, r = BASE[f]
        if list(ps) != sorted(ps) or len(set(ps)) != k:
            return None
        l, r = ren(l, ps), ren(r, ps)
    else:
        sd = tsides(f, list(ps))
        if sd is None:
            return None
        l, r = sd
    if rev:
        l, r = tuple(reversed(l)), tuple(reversed(r))
    return tuple(l), tuple(r)

def apply_all(w, steps):
    w = tuple(w)
    for fam, ps, d, pos in steps:
        l, r = any_sides(fam, ps)
        a, b = (l, r) if d else (r, l)
        assert w[pos:pos + len(a)] == a, (w, fam, ps, d, pos)
        w = w[:pos] + b + w[pos + len(a):]
    return w

def disjoint(g, h):
    return not (set(g[1:]) & set(h[1:]))

def swap_step(g, h, pos):
    """The step turning [g, h] into [h, g] at pos (disjoint letters)."""
    tg, th = g[0], h[0]
    if tg == 'x' and th == 'x': return ('r2a', list(g[1:]) + list(h[1:]), True, pos)
    if tg == 'x' and th == 'n': return ('r2b', list(g[1:]) + list(h[1:]), True, pos)
    if tg == 'n' and th == 'x': return ('r2b', list(h[1:]) + list(g[1:]), False, pos)
    if tg == 'x' and th == 'k': return ('r2c', list(g[1:]) + list(h[1:]), True, pos)
    if tg == 'k' and th == 'x': return ('r2c', list(h[1:]) + list(g[1:]), False, pos)
    if tg == 'n' and th == 'n': return ('r2d', [g[1], h[1]], True, pos)
    if tg == 'n' and th == 'k': return ('r2e', list(g[1:]) + list(h[1:]), True, pos)
    if tg == 'k' and th == 'n': return ('r2e', list(h[1:]) + list(g[1:]), False, pos)
    if tg == 'k' and th == 'k': return ('r2f', list(g[1:]) + list(h[1:]), True, pos)
    raise ValueError

def move_block(w, i, j, k):
    """Steps exchanging the adjacent blocks w[i:j] and w[j:k] (all letters disjoint)."""
    w = list(w)
    steps = []
    A, B = w[i:j], w[j:k]
    # move each letter of B leftwards past all of A
    cur = list(w)
    for t in range(len(B)):
        p = j + t  # position of B[t]
        for q in range(p, i + t, -1):
            g, h = cur[q - 1], cur[q]
            assert disjoint(g, h), (g, h)
            steps.append(swap_step(g, h, q - 1))
            cur[q - 1], cur[q] = h, g
    return steps, tuple(cur)

# Lemma 8.7 at n = 4: P'-spellings of the diagonal gates by consecutive
# phase pairs, chosen so that the decoded gadgets merge over one wire s
# (two letters on the lifts b_s = 0, 1 of one edge; or the square of a
# letter whose target is s, which is the CCZ of its controls) and the
# result is idle on s, so one window step finishes it.
#
# Gray order: gcode k = gray (toBits 4 k), wire 0 first, toBits wire 0
# the least significant bit, gray g_w = b_w xor b_{w+1}.
from itertools import product

n = 4
def gcode(k):
    b = [(k >> w) & 1 for w in range(n)] + [0]
    return tuple(b[w] ^ b[w + 1] for w in range(n))
IDX = {gcode(k): k for k in range(2 ** n)}

def pos(a):
    """target wire and the code of a for the consecutive pair a, a + 1."""
    u, v = gcode(a), gcode(a + 1)
    t = [w for w in range(n) if u[w] != v[w]][0]
    return t, u

def flip(x, w): return tuple(b ^ (1 if i == w else 0) for i, b in enumerate(x))

def letter(a, kind):
    """exponent vector of i: p at a is i_a i_{a+1}^-1, p' its inverse."""
    f = [0] * 16
    s = 1 if kind == 'p' else -1
    f[a] += s; f[a + 1] -= s
    return f

def moves(s):
    """the allowed moves for the merge wire s: (name, letters, effect)."""
    out = []
    for a in range(15):
        t, u = pos(a)
        if t == s:                            # a square: the CCZ of the controls
            for kind in ('p',):
                f = [2 * x for x in letter(a, kind)]
                out.append((f'sq{a}', [(a, kind), (a, kind)], f))
            continue
        # the lift with b_s = 0, and its partner with b_s = 1
        if u[s] == 1: continue
        u1 = flip(u, s)
        b = IDX[u1]
        # the partner must be consecutive with the same target
        for c in (b - 1, b):
            if 0 <= c < 15 and pos(c)[0] == t and set((gcode(c), gcode(c + 1))) == {u1, flip(flip(u, t), s)}:
                ka = 'p'                           # i on u (b_s = 0 lift)
                kc = 'p' if gcode(c) == u1 else "p'"   # i on u1
                f = [x + y for x, y in zip(letter(a, ka), letter(c, kc))]
                out.append((f'pr{a}/{c}', [(a, ka), (c, kc)], f))
    return out

def target(gate):
    kind, p = gate
    f = [0] * 16
    for k in range(16):
        x = gcode(k)
        if kind == 'S': f[k] = x[p]
        elif kind == 'CS': f[k] = x[p] * x[p + 1]
        elif kind == 'I': f[k] = 1
    return f

def solve(gate, s):
    ms = moves(s)
    goal = [v % 4 for v in target(gate)]
    best = None
    for ks in product(range(4), repeat=len(ms)):
        tot = [0] * 16
        for k, (_, _, f) in zip(ks, ms):
            if k:
                for i in range(16): tot[i] += k * f[i]
        if [v % 4 for v in tot] == goal:
            cost = sum(k * len(m[1]) for k, m in zip(ks, ms))
            if best is None or cost < best[0]: best = (cost, [(k, m[0], m[1]) for k, m in zip(ks, ms) if k])
    return best

if __name__ == '__main__':
    for a in range(15): print(a, pos(a))
    gates = [('I', 0)] + [('S', p) for p in range(4)] + [('CS', p) for p in range(3)]
    for g in gates:
        for s in range(4):
            if g[0] == 'S' and s == g[1]: continue
            if g[0] == 'CS' and s in (g[1], g[1] + 1): continue
            ms = moves(s)
            if len(ms) > 9: continue
            r = solve(g, s)
            print(g, 's =', s, 'moves', len(ms), '->', r)

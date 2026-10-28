"""The symmetries of token equations of Sec8/D/W3/Sym.lean, mirrored.

`rl1(j, t)` is `WS.rl1 j t` (a letter becomes a placed token, `toP`), `rlS(js, t)` is
`WS.rlS js t`; `rl_ok(N, j, avail, t)` is `WS.rlOK`, `rls_ok` is `WS.rlSOK`.  `x81(N, w, t)`
is the colour exchange of `WS.x81_entry` (the new token, or None), `XT(w)` the token `WS.xT w`.
`perm_words(N)` gives, for every permutation of the wires, a list of adjacent
transpositions realising it (`rlS` relabels wire q to perm[q]).
"""
import itertools

import tok

KIND_AR = {'box': 1, 'zx': 1, 'xz': 1, 'hg': 2}


def tau(j, q):
    return j + 1 if q == j else (j if q == j + 1 else q)


def toP(l):
    k, j = l
    if k in 'HZ':
        return ('p', 1, ((k, 0),), (j,))
    return ('p', 2, ((k, 0),), (j, j + 1))


def rl1(j, t):
    if t[0] == 's':
        p = toP(t[1:])
        return ('p', p[1], p[2], tuple(tau(j, x) for x in p[3]))
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return ('g', Kd, tuple(tau(j, x) for x in tg), tuple((tau(j, w), c) for w, c in cs))
    _, m, w, ps = t
    return ('p', m, w, tuple(tau(j, x) for x in ps))


def rlS(js, t):
    for j in js:
        t = rl1(j, t)
    return t


def ctl(N, cs):
    d = {}
    for w, c in cs:
        if w not in d:
            d[w] = c
    return lambda i: d.get(i) if i < N else None


def ctrl_wires(N, tg, cs):
    c = ctl(N, cs)
    return [i for i in range(N) if c(i) is not None and i not in tg]


def lean_ok(N, t):
    """`Tk.ok`."""
    if t[0] == 's':
        return t[2] + (1 if t[1] in 'HZ' else 2) <= N
    if t[0] == 'g':
        _, Kd, tg, cs = t
        return len(set(tg)) == len(tg) and all(x < N for x in tg) and len(tg) == KIND_AR[Kd]
    _, m, w, ps = t
    return (len(set(ps)) == len(ps) and all(x < N for x in ps) and len(ps) == m
            and all(l[1] + (1 if l[0] in 'HZ' else 2) <= m for l in w))


def both_ctl(N, j, tg, cs):
    cw = ctrl_wires(N, tg, cs)
    return j in cw and j + 1 in cw


def rl_ok(N, j, avail, t):
    if not (j + 2 <= N and lean_ok(N, t)):
        return False
    if t[0] == 'g':
        _, Kd, tg, cs = t
        if both_ctl(N, j, tg, cs):
            return avail(Kd, len(ctrl_wires(N, tg, cs)))
    return True


def rls_ok(N, avail, js, t):
    for j in js:
        if not rl_ok(N, j, avail, t):
            return False
        t = rl1(j, t)
    return True


def perm_of(N, js):
    """The wire map of rlS js: q -> where wire q goes."""
    out = []
    for q in range(N):
        for j in js:
            q = tau(j, q)
        out.append(q)
    return tuple(out)


def perm_words(N):
    """{perm: js} for every permutation, js a shortest word (BFS)."""
    start = tuple(range(N))
    seen = {start: []}
    frontier = [[]]
    while frontier:
        nxt = []
        for js in frontier:
            for j in range(N - 1):
                w = js + [j]
                p = perm_of(N, w)
                if p not in seen:
                    seen[p] = w
                    nxt.append(w)
        frontier = nxt
    return seen


def XT(w):
    return ('p', 1, (('H', 0), ('Z', 0), ('H', 0)), (w,))


def x81(N, w, t):
    """The token of `WS.x81_entry` for [XT w, t, XT w], or None."""
    if t[0] != 'g':
        return None
    _, Kd, tg, cs = t
    if not (w < N and w not in tg and lean_ok(N, t)):
        return None
    c = ctl(N, cs)
    b = c(w)
    if b is None:
        return None
    new = []
    done = False
    for x, col in cs:
        if x == w and not done:
            new.append((x, not b))
            done = True
        else:
            new.append((x, col))
    return ('g', Kd, tg, tuple(new))


def lean_bool(b):
    return 'true' if b else 'false'


def lean_list(js):
    return '[' + ', '.join(map(str, js)) + ']'

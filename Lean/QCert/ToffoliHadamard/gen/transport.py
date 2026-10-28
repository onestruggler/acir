"""Macro table: Coxeter axioms, Figure 7, the KB rules of S8, and the
adjacent transport facts T_j enc(g) T_j = enc(s_j g)."""
from itertools import combinations
from kb import KB, export, replay_plain
from macro import *

AX = coxeter_axioms()
F7 = fig7_axioms()
BASE = [(n, l, r) for (n, l, r) in AX] + [(n, l, r) for (n, l, r) in F7]
NBASE = len(BASE)

def build_kb():
    eqs = [(l, r, i) for i, (_, l, r) in enumerate(AX)]
    kb = KB({g: g for g in range(7)})
    kb.complete(eqs, verbose=False)
    return kb

KBS = build_kb()
TABLE = [(l, r, None) for (_, l, r) in BASE] + export(KBS, NBASE)
NAMES = [n for (n, _, _) in BASE] + [("kb", k) for k in range(len(KBS.rules))]

def kb_reduce(w):
    """normal form and steps with table ids"""
    nf, steps = KBS.reduce(tuple(w))
    return nf, [(i, k + NBASE, d) for (i, k, d) in steps]

def shift(steps, off):
    return [(i + off, k, d) for (i, k, d) in steps]

def undo(steps):
    return [(i, k, not d) for (i, k, d) in reversed(steps)]

def s8_eq(u, v):
    """steps u -> v for T-words with the same permutation"""
    nu, su = kb_reduce(u)
    nv, sv = kb_reduce(v)
    assert nu == nv, (u, v)
    return su + undo(sv)

def fig7_id(n):
    return next(i for i, (nm, _, _) in enumerate(BASE) if nm == ("fig7", n))

PUSH = {}   # (letter T_i, B) -> table id of [T_i, B] = [B, T_i]
for i in range(1, 7):
    PUSH[(i, NL)] = fig7_id(84 + i)          # (85)..(90): x(i,i+1) N = N x(i,i+1)
for i in range(4, 7):
    PUSH[(i, KL)] = fig7_id(87 + i)          # (91)..(93)

def swap_idx(j, i):
    return j + 1 if i == j else (j if i == j + 1 else i)

def act(j, g):
    return (g[0],) + tuple(swap_idx(j, i) for i in g[1:])

def valid(j, g):
    idx = g[1:]
    return not (j in idx and j + 1 in idx)

def gens8():
    G = [N_(a) for a in range(8)]
    G += [X_(a, b) for a, b in combinations(range(8), 2)]
    G += [K_(*q) for q in combinations(range(8), 4)]
    return G

def split(g):
    """encM g = Q + [B] + rev Q for N and K kinds"""
    w = encM(g)
    B = NL if g[0] == 'n' else KL
    p = w.index(B)
    return w[:p], B

def stab_word(c, letters):
    """a reduced word in the given letters for the permutation c (fixing others)"""
    # bubble sort on positions in letters' range
    w = []
    p = list(c)
    changed = True
    while changed:
        changed = False
        for i in letters:
            if p[i] > p[i + 1]:
                p[i], p[i + 1] = p[i + 1], p[i]
                w.append(i)
                changed = True
    # p was sorted by applying transpositions on the right: c * s_w1 * ... = id
    # so c = s_wk ... s_w1 ... careful: verify below
    return w

def transport_steps(j, g):
    lhs = [j] + encM(g) + [j]
    g2 = act(j, g)
    rhs = encM(g2)
    if g[0] == 'x':
        return lhs, rhs, s8_eq(lhs, rhs)
    Q, B = split(g)
    Q2, _ = split(g2)
    letters = range(1, 6) if B == NL else range(4, 6)   # T_i with i in letters..i+1 inside
    # c = Q2^{-1} T_j Q as a permutation
    target = perm_word([j] + Q)
    # find C with perm(Q2 + C) == target
    C = None
    pc = perm_word(Q2[::-1])  # inverse of Q2 (letters are involutions)
    c = tuple(pc[target[s]] for s in range(8))   # c = Q2^{-1} o target
    # reduced word for c using allowed letters
    allowed = list(range(1, 7)) if B == NL else [4, 5, 6]
    # bubble sort c into identity by right multiplication with allowed transpositions
    cur = list(c); W = []
    changed = True
    while changed:
        changed = False
        for i in allowed:
            # right multiply by s_i: cur o s_i swaps values at positions i, i+1
            if cur[i] > cur[i + 1]:
                cur[i], cur[i + 1] = cur[i + 1], cur[i]
                W.append(i); changed = True
    assert cur == list(range(8)), (j, g, c)
    # c o s_W1 o s_W2 ... = id  =>  c = s_Wk ... s_W1 ; as a word (matrix product order) C = Wk ... W1
    C = W[::-1]
    assert perm_word(Q2 + C) == target, (j, g)
    steps = []
    w = lhs
    # 1. [j] + Q -> Q2 + C
    s1 = s8_eq([j] + Q, Q2 + C)
    steps += s1
    w = Q2 + C + [B] + Q[::-1] + [j]
    # 2. push C across B, last letter first
    pos = len(Q2) + len(C) - 1
    for t in reversed(C):
        steps.append((pos, PUSH[(t, B)], True))
        pos -= 1
    # word now Q2 + [B] + C + rev Q + [j]
    off = len(Q2) + 1
    s3 = s8_eq(C + Q[::-1] + [j], Q2[::-1])
    steps += shift(s3, off)
    return lhs, rhs, steps

def all_transport():
    out = []
    for g in gens8():
        for j in range(7):
            if not valid(j, g):
                continue
            l, r, st = transport_steps(j, g)
            assert replay_plain(TABLE, l, st) == tuple(r), (j, g)
            out.append(((j, g), l, r, st))
    return out

if __name__ == "__main__":
    T = all_transport()
    import statistics
    lens = [len(t[3]) for t in T]
    print(len(T), "facts; steps total", sum(lens), "max", max(lens), "mean", statistics.mean(lens))
    by = {}
    for (j, g), l, r, st in T:
        by.setdefault(g[0], []).append(len(st))
    for k, v in by.items():
        print(k, len(v), sum(v), max(v), "word len max", max(len(t[1]) for t in T if t[0][1][0] == k))

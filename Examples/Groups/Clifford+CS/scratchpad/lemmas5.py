# R0 = (T C)^2 = (C T)^2, T = Toff(0;1,2), C = CS_03, derived from the
# three-qubit theory, the schema cx-ccz and the Toffoli rule toff-ccz
# (deriv.l2), step by step.  The route: the phase gadget PP = T C T C^-1
# is fixed by the swap of its controls 2, 3 (S3) — its CX-conjugates are
# PP times named diagonal gates, which commute and cancel — so
# PP = [Toff(0;1,3), CS_02] (S2), with which C commutes by a three-wire
# window; hence C commutes with PP, which is R0.
from deriv import Derivation, show, fp, cczs, norm
from lemmas4 import L

T, T13, T23 = ('TOFF', 0, 1, 2), ('TOFF', 0, 1, 3), ('TOFF', 0, 2, 3)
C3, C3d, C2, C2d = ('CS', 0, 3), ('CSd', 0, 3), ('CS', 0, 2), ('CSd', 0, 2)
D, Dp, E, F = cczs(0, 1, 2), cczs(0, 1, 3), cczs(1, 2, 3), cczs(0, 2, 3)
K, Kd = ('K', 0), ('Kd', 0)
N32, N23, SW = ('CX', 3, 2), ('CX', 2, 3), ('SWAP', 2, 3)
CS13, CS12, CZ13, CZ12 = ('CS', 1, 3), ('CS', 1, 2), ('CZ', 1, 3), ('CZ', 1, 2)
CSd13, CSd12 = ('CSd', 1, 3), ('CSd', 1, 2)
PP3 = [T, C3, T, C3d]
PP2 = [T13, C2, T13, C2d]

def supp(g): return set(g[1:])

def spell(z, t):
    """Barenco's spelling of the CCZ z with the CNOT's target t (a wire
    of z): CS(p,t) CX(q,t) CS(p,t)^-1 CX(q,t) CS(p,q)."""
    p, q = sorted(set(z[1:]) - {t})
    return [('CS', p, t), ('CX', q, t), ('CSd', p, t), ('CX', q, t), ('CS', p, q)]

# ---------------------------------------------------------------- helpers
def comm_name(g, h): return f'comm {show([g])} {show([h])}'

def ensure_comm(g, h):
    """a lemma [g, h] -> [h, g] for diagonal named gates g, h (CS, CSd,
    CZ, CCZ) whose joint support is four wires."""
    name = comm_name(g, h)
    if name in L: return name
    d = Derivation(name, [g, h], [h, g], L)
    if g[0] == 'CCZ' and h[0] == 'CCZ':
        common = supp(g) & supp(h); assert len(common) == 2
        (w,) = tuple(supp(g) - common); (x,) = tuple(supp(h) - common)
        c = ('CX', w, x)                     # c h c = h g: lemma 0's pattern
        d.win(2, 2, [c, c]); d.win(3, 3, [h, h]); d.win(4, 4, [c, c])
        d.delta(2); d.win(1, 3, []); d.win(0, 2, []); d.delta(0)
    elif g[0] == 'CCZ' or h[0] == 'CCZ':
        z, o, zfirst = (g, h, True) if g[0] == 'CCZ' else (h, g, False)
        (a,) = tuple(supp(z) & supp(o))
        t = min(supp(z) - {a})
        pieces = spell(z, t)
        if zfirst:
            d.win(0, 1, pieces)              # pieces o
            for k in range(4, -1, -1):       # o moves left through the pieces
                p = d.cur[k]
                if supp(p) & supp(o): d.win(k, k + 2, [o, p])
                else: d.comm(k)
            d.win(1, 6, [z])
        else:
            d.win(1, 2, pieces)              # o pieces
            for k in range(5):
                p = d.cur[k + 1]
                if supp(p) & supp(o): d.win(k, k + 2, [p, o])
                else: d.comm(k)
            d.win(0, 5, [z])
    else:
        raise ValueError((g, h))
    d.done()
    return name

def swap_adj(d, k):
    """exchange the (commuting, diagonal) gates at k, k+1 by the right move."""
    g, h = d.cur[k], d.cur[k + 1]
    if not (supp(g) & supp(h)): d.comm(k)
    elif len(supp(g) | supp(h)) <= 3: d.win(k, k + 2, [h, g])
    else: d.lemma(ensure_comm(g, h), k)

KEY = {'CZ': 0, 'CS': 1, 'CSd': 1, 'CCZ': 2}
def key(g): return (KEY[g[0]], g[1:])

def sort_diag(d, i, j):
    """bubble-sort the diagonal window [i, j) into the canonical order and
    cancel what cancels; returns the new end."""
    n = j - i
    while True:
        for _ in range(n):
            for k in range(i, i + n - 1):
                if key(d.cur[k]) > key(d.cur[k + 1]): swap_adj(d, k)
        changed = False; k = i
        while k + 1 < i + n:
            g, h = d.cur[k], d.cur[k + 1]
            if g[1:] == h[1:] and ((g[0] == h[0] and g[0] in ('CZ', 'CCZ')) or {g[0], h[0]} == {'CS', 'CSd'}):
                d.win(k, k + 2, []); n -= 2; changed = True; continue
            if g[0] == 'CS' and h[0] == 'CS' and g[1:] == h[1:]:
                d.win(k, k + 2, [('CZ',) + g[1:]]); n -= 1; changed = True; continue
            k += 1
        if not changed: return i + n

def diag_form(word):
    """the canonical form sort_diag reaches (on a scratch derivation)."""
    d = Derivation('scratch', word, word, L)
    e = sort_diag(d, 0, len(word))
    return d.cur[:e]

# ------------------------------------------------------- the basic lemmas
# E passes T (two CCZs sharing wires 1, 2 commute, under K_0)
d = Derivation('E-T', [E, T], [T, E], L)
d.win(1, 2, [K, D, Kd]); d.comm(0); d.lemma('CCZ312-CCZ012', 1); d.comm(2); d.win(0, 3, [T]); L = d.done()

# T T13 = T13 T (two CCZs sharing wires 0, 1 commute, under K_0)
ensure_comm(D, Dp)
d = Derivation('T-T13', [T, T13], [T13, T], L)
d.win(0, 1, [K, D, Kd]); d.win(3, 4, [K, Dp, Kd]); d.win(2, 4, [])
d.lemma(comm_name(D, Dp), 1); d.win(2, 2, [Kd, K]); d.win(0, 3, [T13]); d.win(1, 4, [T]); L = d.done()

# a diagonal gate off wire 0 passes T: the CCZ of T spelled with its CNOT's
# target off the gate
def pass_T(g):
    name = f'{show([g])} passes T'
    if name in L: return name
    d = Derivation(name, [g, T], [T, g], L)
    if supp(g) <= {0, 1, 2}:
        d.win(0, 2, [T, g])
    elif g == E:
        d.lemma('E-T', 0)
    else:
        assert 0 not in supp(g)
        t = min({1, 2} - supp(g))
        d.win(1, 2, [K] + spell(D, t) + [Kd])
        d.comm(0)                            # g K -> K g
        for k in range(1, 6):
            p = d.cur[k + 1]
            if supp(p) & supp(g): d.win(k, k + 2, [p, g])
            else: d.comm(k)
        d.comm(6)                            # g Kd -> Kd g
        d.win(0, 7, [T])
    d.done(); return name

# Dp T = T Dp E and F T = T F E: the Toffoli rule
d = Derivation(f'{show([Dp])}-T', [Dp, T], [T, Dp, E], L)
d.win(0, 0, [T, T]); d.l2(1); L = d.done()
d = Derivation(f'{show([F])}-T', [F, T], [T, F, E], L)
d.win(0, 0, [T, T]); d.l2(1); L = d.done()

# every named diagonal gate passes PP3
def pass_PP(g):
    name = f'{show([g])} passes PP3'
    if name in L: return name
    d = Derivation(name, [g] + PP3, PP3 + [g], L)
    if g == D:
        d.win(0, 2, [T, D, CZ12])                  # T D CZ12 C3 T C3d
        swap_adj(d, 2); swap_adj(d, 1)             # T C3 D CZ12 T C3d
        d.win(2, 5, [T, D])                        # T C3 T D C3d
        swap_adj(d, 3)
    elif g in (Dp, F):
        d.lemma(f'{show([g])}-T', 0)               # T g E C3 T C3d
        swap_adj(d, 2); swap_adj(d, 1)             # T C3 g E T C3d
        d.lemma('E-T', 3); d.lemma(f'{show([g])}-T', 2)   # T C3 T g E E C3d
        d.win(4, 6, []); swap_adj(d, 3)
    else:
        d.lemma(pass_T(g), 0); swap_adj(d, 1); d.lemma(pass_T(g), 2); swap_adj(d, 3)
    d.done(); return name

# ------------------------------------------- the CX-conjugates of the gadget
# N32 T N32 = T T13 (the schema under K_0), N23 T N23 = T (letter by letter)
d = Derivation('N32-T', [N32, T, N32], [T, T13], L)
d.win(1, 2, [K, D, Kd]); d.comm(0); d.comm(3); d.delta(1)
d.win(2, 2, [Kd, K]); d.win(0, 3, [T]); d.win(1, 4, [T13]); L = d.done()

def conj_T_letters(name, c, result, rename=None):
    """c T c = result, c on wires 2, 3: T's CCZ spelled with the CNOT's
    target 1, each piece conjugated by c in a window."""
    d = Derivation(name, [c, T, c], result, L)
    d.win(1, 2, [K] + spell(D, 1) + [Kd]); d.comm(0)
    for k in range(1, 6):
        p = d.cur[k + 1]
        if supp(p) & supp(c):
            q = (p[0],) + (tuple(rename(w) for w in p[1:]) if rename else p[1:])
            d.win(k, k + 2, [q, c])
        else: d.comm(k)
    d.comm(6); d.win(7, 9, []); d.win(0, 7, result)
    return d.done()

L = conj_T_letters('N23-T', N23, [T])
L = conj_T_letters('SW-T-SW', SW, [T13], rename=lambda w: {2: 3, 3: 2}.get(w, w))

# N32 PP3 N32 = CS13 Dp E PP3
d = Derivation('N32-PP3', [N32] + PP3 + [N32], [CS13, Dp, E] + PP3, L)
for k in (4, 3, 2): d.win(k, k, [N32, N32])             # (N32 T N32)(N32 C3 N32)(N32 T N32)(N32 C3d N32)
d.lemma('N32-T', 0); d.win(2, 5, [C3]); d.lemma('N32-T', 3); d.win(5, 8, [C3d])
d.lemma('T-T13', 3)                                      # T T13 C3 T13 T C3d
d.win(1, 4, [CS13, Dp, C3])                              # T13 C3 T13 = m C3
d.win(3, 3, [T, T])                                      # T CS13 Dp T T C3 T C3d
d.lemma(pass_T(CS13), 0, forward=False)                  # CS13 T Dp T T C3 T C3d
d.l2(1)                                                  # CS13 Dp E T C3 T C3d
L = d.done()

# N23 PP3 N23 = PP3 CS12 D E
d = Derivation('N23-PP3', [N23] + PP3 + [N23], PP3 + [CS12, D, E], L)
for k in (4, 3, 2): d.win(k, k, [N23, N23])
d.lemma('N23-T', 0); d.win(1, 4, [C3, C2, F]); d.lemma('N23-T', 4); d.win(5, 8, [F, C2d, C3d])
d.lemma(f'{show([F])}-T', 3)                                         # T C3 C2 T F E F C2d C3d
d.lemma(ensure_comm(E, F), 4, forward=False); d.win(5, 7, [])   # T C3 C2 T E C2d C3d
d.win(2, 4, [T, C2, CS12, D])                             # T C3 T C2 CS12 D E C2d C3d
swap_adj(d, 6); swap_adj(d, 5); swap_adj(d, 4); d.win(3, 5, [])   # T C3 T CS12 D E C3d
swap_adj(d, 5); swap_adj(d, 4); swap_adj(d, 3)
L = d.done()

# N23 D N23 = D
d = Derivation('N23-D', [N23, D, N23], [D], L)
d.win(1, 2, spell(D, 1))
for k in range(5):
    p = d.cur[k + 1]
    if supp(p) & supp(N23): d.win(k, k + 2, [p, N23])
    else: d.comm(k)
d.win(5, 7, []); d.win(0, 5, [D]); L = d.done()

# ---------------------------------------------------------- S3, S2, R0
# the swap of the controls 2, 3 fixes PP3
d = Derivation('S3', [SW] + PP3 + [SW], PP3, L)
d.win(0, 1, [N23, N32, N23]); d.win(7, 8, [N23, N32, N23])   # N23 N32 N23 PP3 N23 N32 N23
d.lemma('N23-PP3', 2)                                        # N23 N32 PP3 CS12 D E N32 N23
d.win(6, 6, [N32, N32])                                      # N23 N32 PP3 N32 N32 CS12 D E N32 N23
d.lemma('N32-PP3', 1)                                        # N23 CS13 Dp E PP3 N32 CS12 D E N32 N23
d.win(11, 11, [N32, N32]); d.win(10, 10, [N32, N32])         # … N32 CS12 N32 N32 D N32 N32 E N32 N23
d.win(8, 11, [CS12, CS13, E]); d.delta(11); d.win(13, 16, [E, CZ13])
# N23 CS13 Dp E PP3 CS12 CS13 E D Dp E CZ13 N23: PP3 to the right
for idx, g in enumerate((CS12, CS13, E, D, Dp, E, CZ13)):
    d.lemma(pass_PP(g), 4 + idx, forward=False)
e = sort_diag(d, 1, 11)
assert d.cur[1:e] == [CS12, D, E], show(d.cur)
for k in range(e - 1, 0, -1):                                # the diagonals to the right of PP3
    d.lemma(pass_PP(d.cur[k]), k)
d.win(5, 5, [N23, N23])                                      # N23 PP3 N23 N23 CS12 D E N23
d.lemma('N23-PP3', 0)                                        # PP3 CS12 D E N23 CS12 D E N23
d.win(10, 10, [N23, N23]); d.win(9, 9, [N23, N23])
d.win(7, 10, [CS12]); d.lemma('N23-D', 8); d.win(9, 12, [E, CZ12])
e = sort_diag(d, 4, len(d.cur))
assert e == 4, show(d.cur)
L = d.done()

# PP3 = PP2: conjugate by the swap, letter by letter
d = Derivation('S2', PP3, PP2, L)
d.lemma('S3', 0, forward=False)                              # SW T C3 T C3d SW
for k in (4, 3, 2): d.win(k, k, [SW, SW])
d.lemma('SW-T-SW', 0); d.win(1, 4, [C2]); d.lemma('SW-T-SW', 2); d.win(3, 6, [C2d])
L = d.done()

# C commutes with PP2 (windows on wires 0, 1, 3), hence with PP3
d = Derivation('C3-PP3', [C3] + PP3, PP3 + [C3], L)
d.lemma('S2', 1)                                             # C3 T13 C2 T13 C2d
d.win(0, 2, [T13, CS13, Dp, C3])                             # T13 CS13 Dp C3 C2 T13 C2d
swap_adj(d, 2); swap_adj(d, 1)                               # T13 C3 CS13 Dp C2 T13 C2d
swap_adj(d, 3); swap_adj(d, 2)                               # T13 C3 C2 CS13 Dp T13 C2d
d.win(3, 6, [T13, CSd13, Dp])                                # T13 C3 C2 T13 CSd13 Dp C2d
d.win(1, 3, [C2, C3]); d.win(2, 4, [T13, CS13, Dp, C3])      # T13 C2 T13 CS13 Dp C3 CSd13 Dp C2d
d.win(5, 7, [CSd13, C3]); d.win(6, 8, [Dp, C3])              # T13 C2 T13 CS13 Dp CSd13 Dp C3 C2d
d.win(3, 7, []); d.win(3, 5, [C2d, C3])                      # T13 C2 T13 C2d C3
d.lemma('S2', 0, forward=False)
L = d.done()

d = Derivation('R0', [T, C3, T, C3], [C3, T, C3, T], L)
d.win(3, 4, [C3d, C3, C3]); d.lemma('C3-PP3', 0, forward=False); d.win(4, 6, [])
L = d.done()
print('lemmas:', len(L))

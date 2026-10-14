# The rotation ROT = CK10 B S1 CK10 B (B the box with its box wire on
# wire 1, dec.py's G_rot at n = 4) squares to E = CCZ_123, derived from
# PP^2 = E: the box is the gate CCZ_023 (Lemma 1 under K_1), so
# ROT = [CK10, CCZ_023]; under K_0 that is [CK10, Toff(0;2,3)], under the
# swap of wires 1, 3 it is [CK30, Toff(0;1,2)]^-1, and U0 PP U0^-1 is
# [Toff(0;1,2), CK30] by windows, U = K^-1 S K.  So ROT is a conjugate
# of PP^-1 and ROT^2 of PP^-2 = E.
from deriv import Derivation, show, fp, cczs, norm
import lemmas5 as L5
from lemmas5 import (L, ensure_comm, swap_adj, spell, supp,
                     T, T13, T23, C3, C3d, C2, C2d, D, Dp, E, F, K, Kd, CS13, CZ13, PP3)

T1 = ('TOFF', 1, 0, 2)
c, cd, s = ('CK', 1, 0), ('CKd', 1, 0), ('S', 1)
CK30, CKd30, CK20, CKd20, CK10, CKd10 = ('CK', 3, 0), ('CKd', 3, 0), ('CK', 2, 0), ('CKd', 2, 0), ('CK', 1, 0), ('CKd', 1, 0)
CX30, CX31, CX12 = ('CX', 3, 0), ('CX', 3, 1), ('CX', 1, 2)
S3, S3d, S0, S0d = ('S', 3), ('Sd', 3), ('S', 0), ('Sd', 0)
K1, K1d = ('K', 1), ('Kd', 1)
SW12, SW23 = ('SWAP', 1, 2), ('SWAP', 2, 3)
SW13w = [SW12, SW23, SW12]
U, Ui = [Kd, S0, K], [Kd, S0d, K]            # U0 = K0^-1 S0 K0 and its inverse
B = [D, T1, CZ13, T1, D, CZ13]
ROT = [c] + B + [s, c] + B
PPi = [C3, T, C3d, T]
CZ03 = ('CZ', 0, 3)

def rename(g, f):
    return (g[0],) + tuple(f(w) for w in g[1:])

# a CCZ passes a gate h it commutes with, by a spelling whose pieces each
# commute with h in a window or are disjoint from it
def ensure_pass(z, h):
    name = f'{show([z])} passes {show([h])}'
    if name in L: return name
    for t in sorted(supp(z)):
        pieces = spell(z, t)
        ok = all((not (supp(p) & supp(h))) or
                 (len(supp(p) | supp(h)) <= 3 and fp([p, h]) == fp([h, p])) for p in pieces)
        if not ok: continue
        d = Derivation(name, [z, h], [h, z], L)
        d.win(0, 1, pieces)
        for k in range(4, -1, -1):
            p = d.cur[k]
            if supp(p) & supp(h): d.win(k, k + 2, [h, p])
            else: d.comm(k)
        d.win(1, 6, [z]); d.done(); return name
    raise ValueError((z, h))

# conjugation of the letter at k+1 by the swap at k and k+2 (adjacent
# wires i, i+1): a window, a commutation, or letter by letter for a CCZ
# or a Toffoli
def swap_conj(d, k):
    sw, g = d.cur[k], d.cur[k + 1]
    assert sw[0] == 'SWAP' and d.cur[k + 2] == sw
    i, j = sw[1:]
    f = lambda w: j if w == i else i if w == j else w
    if g[0] in ('CCZ', 'TOFF'):
        if g[0] == 'TOFF':
            t = g[1]; z = cczs(*g[1:]); kt, ktd = ('K', t), ('Kd', t)
            d.win(k + 1, k + 2, [kt, z, ktd])              # sw K z Kd sw
            d.win(k + 3, k + 3, [sw, sw])                   # sw K z sw sw Kd sw
            swap_conj(d, k + 4)                             # sw K z sw Kd'
            d.win(k + 2, k + 2, [sw, sw])                   # sw K sw sw z sw Kd'
            swap_conj(d, k + 3)                             # sw K sw z' Kd'
            swap_conj(d, k)                                 # K' z' Kd'
            d.win(k, k + 3, [rename(g, f)])
        else:
            pieces = spell(g, min(supp(g)))
            d.win(k + 1, k + 2, pieces)                     # sw p1 .. p5 sw
            for m in range(4):                              # the swap pairs between the pieces
                d.win(k + 2 + 3 * m, k + 2 + 3 * m, [sw, sw])
            for m in range(4, -1, -1): swap_conj(d, k + 3 * m)
            d.win(k, k + 5, [rename(g, f)])
        return
    if not (supp(g) & supp(sw)):
        d.comm(k + 1); d.win(k, k + 2, [])
    else:
        d.win(k, k + 3, [rename(g, f)])

# ----------------------------------------------------------- the box is F
d = Derivation('T1-CZ13-T1', [T1, CZ13, T1], [F, CZ13], L)
d.win(0, 1, [K1, D, K1d]); d.win(4, 5, [K1, D, K1d]); d.win(2, 5, [CX31])
d.win(1, 1, [CX31, CX31]); d.delta(2); d.lemma(ensure_comm(F, D), 3); d.win(2, 4, [])
d.lemma(ensure_pass(F, CX31), 1, forward=False); d.comm(0); d.win(1, 4, [CZ13]); L.update(d.done())

d = Derivation('B=F', B, [F], L)
d.lemma('T1-CZ13-T1', 1); d.lemma(ensure_comm(D, F), 0); d.lemma(ensure_comm(D, CZ13), 1)
d.win(2, 4, []); d.win(1, 3, []); L.update(d.done())

d = Derivation('ROT=[c,F]', ROT, [c, F, cd, F], L)
d.lemma('B=F', 1); d.lemma('B=F', 4); d.win(2, 4, [cd]); L.update(d.done())

# ---------------------------------------------- under K0: [CK10, Toff(0;2,3)]
d = Derivation('Rk', [Kd, c, F, cd, F, K], [c, T23, cd, T23], L)
d.win(4, 4, [K, Kd]); d.win(3, 3, [K, Kd]); d.win(2, 2, [K, Kd])
d.win(0, 3, [c]); d.win(1, 4, [T23]); d.win(2, 5, [cd]); d.win(3, 6, [T23]); L.update(d.done())

# ------------------------------- under the swap of wires 1, 3: [CK30, T]^-1
d = Derivation('SW13-Rk', SW13w + [c, T23, cd, T23] + SW13w, [CK30, T, CKd30, T], L)
# the three swaps of SW13 move in one at a time: SW12 SW23 (SW12 w SW12) SW23 SW12
for sw_, lo, hi in ((SW12, 2, 7), (SW23, 1, 6), (SW12, 0, 5)):
    # conjugate each of the four letters by the innermost swap pair
    for k in (hi - 1, hi - 2, hi - 3): d.win(k, k, [sw_, sw_])
    for k in (lo + 9, lo + 6, lo + 3, lo): swap_conj(d, k)
L.update(d.done())

# ---------------------------------------- U0 PP U0^-1 = [T, CK30], and inverse
def conj_U(name, word, result):
    d = Derivation(name, U + word + Ui, result, L)
    for k in range(len(word) - 1, 0, -1): d.win(3 + k, 3 + k, Ui + U)
    pos = 0
    for g in word:
        if g[0] == 'TOFF': d.win(pos, pos + 7, [g]); pos += 1
        elif g == C3: d.win(pos, pos + 7, [CK30, CX30, S3]); pos += 3
        elif g == C3d: d.win(pos, pos + 7, [S3d, CX30, CKd30]); pos += 3
        else: raise ValueError(g)
    return d

d = conj_U('PU', PP3, [T, CK30, T, CKd30])
# T CK30 CX30 S3 T S3d CX30 CKd30
d.comm(3); d.win(4, 6, [])                                   # T CK30 CX30 T CX30 CKd30
d.win(3, 4, [CKd20, C2, CK20, CX12, CKd20, C2d, CK20, CX12, CKd10, ('CS', 0, 1), CK10])
d.win(2, 6, [CKd20, C2, CK20, CX30]); d.comm(5); d.win(6, 10, [CKd20, C2d, CK20, CX30])
d.comm(9); d.win(10, 14, [CKd10, ('CS', 0, 1), CK10, CX30]); d.win(13, 15, [])
d.win(2, 13, [T]); L.update(d.done())

d = conj_U('PUinv', PPi, [CK30, T, CKd30, T])
# CK30 CX30 S3 T S3d CX30 CKd30 T
d.comm(2); d.win(3, 5, [])                                   # CK30 CX30 T CX30 CKd30 T
d.win(2, 3, [CKd20, C2, CK20, CX12, CKd20, C2d, CK20, CX12, CKd10, ('CS', 0, 1), CK10])
d.win(1, 5, [CKd20, C2, CK20, CX30]); d.comm(4); d.win(5, 9, [CKd20, C2d, CK20, CX30])
d.comm(8); d.win(9, 13, [CKd10, ('CS', 0, 1), CK10, CX30]); d.win(12, 14, [])
d.win(1, 12, [T]); L.update(d.done())

# -------------------------------------------------- PP^2 = E and PP^-2 = E
d = Derivation('C3d-A', [C3d, T, C3, T], [T, C3, T, C3d], L)
d.win(0, 1, [C3, C3, C3])
for k in (2, 1, 0): d.lemma('R0', k, forward=False)
d.win(3, 6, [C3d]); L.update(d.done())

d = Derivation('PP2=E', PP3 + PP3, [E], L)
d.lemma('C3d-A', 3); d.win(2, 4, []); d.win(1, 3, [CZ03]); d.win(3, 5, [CZ03])
d.lemma('T-CZ03-T', 0); d.win(1, 3, []); L.update(d.done())

d = Derivation('C3-Ai', [C3, T, C3d, T], [T, C3d, T, C3], L)
d.win(0, 0, [T, T]); d.win(1, 1, [C3d, C3]); d.lemma('R0', 2, forward=False); d.win(5, 7, []); d.win(4, 6, [])
L.update(d.done())

d = Derivation('PPi2=E', PPi + PPi, [E], L)
d.lemma('C3-Ai', 4); d.win(3, 5, []); d.win(2, 4, [CZ03]); d.lemma('T-CZ03-T', 1)
d.lemma(ensure_comm(E, C3), 0, forward=False); d.win(1, 4, []); L.update(d.done())

# ------------------------------------------------ ROT as a conjugate of PP^-1
d = Derivation('ROT-form', [c, F, cd, F], [K] + SW13w + U + PPi + Ui + SW13w + [Kd], L)
d.win(0, 0, [K, Kd]); d.win(6, 6, [K, Kd]); d.lemma('Rk', 1)
d.win(5, 5, SW13w + SW13w); d.win(1, 1, SW13w + SW13w)
d.lemma('SW13-Rk', 4); d.lemma('PUinv', 4, forward=False); L.update(d.done())

d = Derivation('ROT2=E', ROT + ROT, [E], L)
d.lemma('ROT=[c,F]', 0); d.lemma('ROT=[c,F]', 4); d.lemma('ROT-form', 0); d.lemma('ROT-form', 18)
d.win(17, 19, []); d.win(14, 20, []); d.win(11, 17, [])
d.lemma('PPi2=E', 7); d.comm(7); d.comm(8); d.comm(9); d.win(4, 10, [])
d.win(3, 6, [E]); d.win(2, 5, [E]); d.win(1, 4, [E]); d.comm(0); d.win(1, 3, [])
L.update(d.done())
print('lemmas:', len(L))

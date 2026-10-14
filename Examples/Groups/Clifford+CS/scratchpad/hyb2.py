# Refine hyb1: (A, B) with [A, B] = G1 and A = V^2 a square in C1, so
# that CC(A) is Barenco's word of two-wire gates
#   CC(A) = C_{c2}(V) CX_{c1->c2} C_{c2}(V^-1) CX_{c1->c2} C_{c1}(V)
# (time order), and check that identity on 3 wires with the controlled
# functor C(S) = CS, C(K) = CK, C(i) = S_c.
from gadgets import *
import hyb1
els = hyb1.els; key2 = hyb1.key2; I2 = hyb1.I2; det2 = hyb1.det2; order = hyb1.order
G1a, G1b = hyb1.G1a, hyb1.G1b

sq = {}                                   # key of V^2 -> a V word
for V, wv in els:
    k = key2(mul2(V, V))
    if k not in sq or len(wv) < len(sq[k][1]): sq[k] = (V, wv)

for name, T in (('G1 (a at t=0)', G1a), ('G1 (a at t=1)', G1b)):
    sols = []
    for A, wa in els:
        if key2(A) not in sq: continue
        V, wv = sq[key2(A)]
        Ai = inv2(A)
        for B, wb in els:
            if mul2(A, mul2(B, mul2(Ai, inv2(B)))) == T:
                sols.append((len(wv) + len(wb), wa or 'e', wv or 'e', wb or 'e', det2(B)))
    sols.sort()
    print(name, len(sols), 'pairs with A a square; shortest:')
    for s in sols[:8]: print('   A =', s[1], '= V^2, V =', s[2], '| B =', s[3], 'det B', s[4])

# The controlled functor on one qubit, as words on wires (c, t).
def ctrlw(word1, c, t):
    out = []
    for g in word1:
        if g == 'S': out.append(('CS', c, t))
        elif g == 'K': out.append(('CK', c, t))
        elif g == 'i': out.append(('S', c))
        else: raise ValueError(g)
    return out
def inv1(word1):
    out = []
    for g in reversed(word1):
        if g == 'S': out += ['S', 'S', 'S']
        elif g == 'K': out += ['K', 'i']
        elif g == 'i': out += ['i', 'i', 'i']
    return out
def barenco(wv, c1, c2, t):
    # time order: C_{c2}V, CX, C_{c2}V^-1, CX, C_{c1}V  -> word order reversed
    # operator order (the reverse of the time order); ctrlw is already in operator order
    return ctrlw(wv, c1, t) + [('CX', c1, c2)] + ctrlw(inv1(wv), c2, t) + [('CX', c1, c2)] + ctrlw(wv, c2, t)

ok = True
for name, T in (('G1a', G1a), ('G1b', G1b)):
    # take the shortest square solution
    best = None
    for A, wa in els:
        if key2(A) not in sq: continue
        V, wv = sq[key2(A)]
        Ai = inv2(A)
        for B, wb in els:
            if mul2(A, mul2(B, mul2(Ai, inv2(B)))) == T:
                if best is None or len(wv) + len(wb) < len(best[0]) + len(best[1]): best = (wv, wb, A, B)
    wv, wb, A, B = best
    # CC(A) on wires t=0, c1=1, c2=2 by Barenco, compared with ctrl_spec
    Acc = ctrl_spec(3, 0, [1, 2], A)
    ok &= check(f'{name}: Barenco CC(A) with V = {wv}', matrix(3, barenco(list(wv), 1, 2, 0)) == Acc)
    # the hybrid at n = 4: [L_{1,2}(A), L_{3}(B)] on target 0
    n = 4
    LA = barenco(list(wv), 1, 2, 0)
    LB = ctrlw(list(wb), 3, 0)
    LAi = inverse(LA); LBi = inverse(LB)
    word = LA + LB + LAi + LBi            # word order: A B A^-1 B^-1, rightmost first... fix below
    # matrix(word) multiplies left to right as operator product: [A][B][A^-1][B^-1] = A B A^-1 B^-1 as operators
    M4 = matrix(n, LA + LB + LAi + LBi)
    spec = ctrl_spec(n, 0, [1, 2, 3], T)
    ok &= check(f'{name}: L^3(G1) = [L_12 A, L_3 B] at n = 4 (B = {wb})', M4 == spec)
print('ALL OK' if ok else 'SOME FAILED')

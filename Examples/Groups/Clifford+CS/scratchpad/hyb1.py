# The hybrid letter with its sink on the pair is a 1-qubit gate under
# n - 1 controls: G1 = K . diag(-i, 1) (a at t = 0) or its mirror
# X K X . diag(1, -i) (a at t = 1).  Search the 1-qubit Clifford group
# C1 = <S, K, i> (96 elements) for G1 = [A, B] with det A = +-1, so that
# L^{n-1}(G1) = L_{C1}(A) L_{C2}(B) L_{C1}(A^-1) L_{C2}(B^-1), |C1| = 2,
# is a circuit at n = 4 (L_{C1}(A) a 3-wire gate of det +-1, L_{C2}(B)
# with two idle wires).  Also: which A have cheap CC-A words.
from gadgets import *

gens = {'S': G_S, 'K': G_K, 'i': {(0, 0): I_, (0, 1): ZERO, (1, 0): ZERO, (1, 1): I_}}
I2 = {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): ONE}
key2 = lambda A: tuple(sorted((k, (v.r, v.i)) for k, v in A.items()))
group = {key2(I2): (I2, '')}
frontier = [(I2, '')]
while frontier:
    nxt = []
    for A, w in frontier:
        for g, G in gens.items():
            B = mul2(A, G)
            kb = key2(B)
            if kb not in group:
                group[kb] = (B, w + g); nxt.append((B, w + g))
    frontier = nxt
els = list(group.values())
print(len(els), 'elements')
det2 = lambda A: A[(0, 0)] * A[(1, 1)] - A[(0, 1)] * A[(1, 0)]
def order(A):
    P, k = A, 1
    while P != I2:
        P = mul2(P, A); k += 1
    return k

Dm = {(0, 0): MI, (0, 1): ZERO, (1, 0): ZERO, (1, 1): ONE}
G1a = mul2(G_K, Dm)                                   # a at t = 0
XKX = mul2(G_X, mul2(G_K, G_X))
G1b = mul2(XKX, {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): MI})   # a at t = 1
for name, T in (('G1 (a at t=0)', G1a), ('G1 (a at t=1)', G1b)):
    print(name, 'det', det2(T), 'order', order(T))
    sols = []
    for A, wa in els:
        if det2(A) not in (ONE, NEG): continue
        Ai = inv2(A)
        for B, wb in els:
            if mul2(A, mul2(B, mul2(Ai, inv2(B)))) == T:
                sols.append((wa or 'e', order(A), det2(A), wb or 'e', order(B), det2(B)))
    print(' ', len(sols), 'pairs (A, B) with det A = +-1')
    # the shortest few, and whether some A is a phased Pauli (order <= 4 with A^2 scalar)
    sols.sort(key=lambda s: (len(s[0]) + len(s[3]), s[0], s[3]))
    for s in sols[:12]: print('   A =', s[0], 'ord', s[1], 'det', s[2], '| B =', s[3], 'ord', s[4], 'det', s[5])

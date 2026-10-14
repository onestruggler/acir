# Pushing C = CS_03 through Barenco's decomposition of T = Toff(0;1,2):
# for each square root V of X in the 1-qubit Clifford group, the
# correction M = V^-1 S V S^-1 (C Lambda_1(V_0) C^-1 = Lambda_1(V_0) . Lambda_13(M_0)).
from gadgets import *
import hyb1
els = hyb1.els; I2 = hyb1.I2; key2 = hyb1.key2
roots = [(V, w) for V, w in els if mul2(V, V) == G_X]
print('square roots of X:', [w for _, w in roots])
def name(A):
    for B, w in els:
        if B == A: return w or 'e'
    return '?'
def diag(A): return A[(0, 1)] == ZERO and A[(1, 0)] == ZERO
for V, w in roots:
    M = mul2(inv2(V), mul2(G_S, mul2(V, inv2(G_S))))
    Mp = mul2(V, mul2(G_S, mul2(inv2(V), inv2(G_S))))
    print(f'V = {w}: M = V^-1 S V S^-1 = {name(M)} diagonal={diag(M)}: {M}')
    print(f'          M\' = V S V^-1 S^-1 = {name(Mp)} diagonal={diag(Mp)}')
# and the 3-wire check of the conjugation formula on wires (0,1,3) for V = the first root
V, w = roots[0]
# word for Lambda_1(V_0) as C(V) with control 1 target 0, V given as a string of S,K,i
def ctrlw(word1, c, t):
    return [{'S': ('CS', c, t), 'K': ('CK', c, t), 'i': ('S', c)}[g] for g in word1]
Cw = [('CS', 0, 3)]
p = ctrlw(w, 1, 0)
lhs = matrix(4, Cw + p + inverse(Cw))
M = mul2(inv2(V), mul2(G_S, mul2(V, inv2(G_S))))
rhs = matrix(4, p) * ctrl_spec(4, 0, [1, 3], M)
print('C p C^-1 == p . Lambda_13(M_0):', lhs == rhs)

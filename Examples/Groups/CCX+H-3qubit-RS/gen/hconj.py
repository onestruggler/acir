"""Short Sigma_1 words for H2 g H2, by a breadth-first search over matrices."""
from fractions import Fraction as Fr
from model import GATES, mul, mat, key, bits, N, ID

M2 = [[Fr(0)] * N for _ in range(N)]
for r in range(N):
    for c in range(N):
        br, bc = bits(r), bits(c)
        if br[0] == bc[0] and br[1] == bc[1]:
            M2[r][c] = Fr((-1) ** (br[2] * bc[2]))


def hconj(A):
    B = mul(mul(M2, A), M2)
    return [[x / 2 for x in row] for row in B]


S1 = [g for g in GATES]
CHAIN = ['X0', 'CX01', 'CCX12', 'CCZ', 'K12', 'NK', 'X1', 'CX20', 'CX21', 'CX12', 'SW12', 'CX02', 'SW02',
         'K01', 'CX10', 'SW01', 'CCX02', 'X2', 'CZ01', 'Z0', 'Z2', 'Z1', 'CCX01', 'CZ02', 'CZ12']


def table(depth=3):
    seen = {key(ID): ()}
    frontier = [((), ID)]
    for d in range(depth):
        nf = []
        for (w, M) in frontier:
            for g in S1:
                M2_ = mul(M, GATES[g])
                k = key(M2_)
                if k not in seen:
                    seen[k] = w + (g,)
                    nf.append((w + (g,), M2_))
        frontier = nf
    return seen


if __name__ == '__main__':
    T = table(3)
    out = {}
    for g in CHAIN:
        k = key(hconj(GATES[g]))
        out[g] = T.get(k)
        print(g, out[g])

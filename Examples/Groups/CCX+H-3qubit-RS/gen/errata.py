"""Check every claim of ERRATA.md on the matrices.

For each printed equation that is false, print one entry at which its two
sides differ; for each correction, check that it holds.  Exact arithmetic
over the rationals, basis state 4 x0 + 2 x1 + x2, products in operator
order (the rightmost factor acts first), as in model.py.

    python3 errata.py
"""
import itertools
from fractions import Fraction as Fr

from model import GATES, ID, N, mul

# Two-level operators of Li, Ross and Selinger on the 8 basis states.


def Xab(a, b):
    M = [row[:] for row in ID]
    M[a][a] = M[b][b] = Fr(0)
    M[a][b] = M[b][a] = Fr(1)
    return M


def Mi(a):
    M = [row[:] for row in ID]
    M[a][a] = Fr(-1)
    return M


def Kabcd(a, b, c, d):
    ix = (a, b, c, d)
    M = [row[:] for row in ID]
    for i in range(4):
        for j in range(4):
            s = (-1) ** ((i >> 1) * (j >> 1) + (i & 1) * (j & 1))
            M[ix[i]][ix[j]] = Fr(s, 2)
    return M


def prod(*ms):
    P = ID
    for m in ms:
        P = mul(P, m if isinstance(m, list) else GATES[m])
    return P


def diff(A, B):
    for r in range(N):
        for c in range(N):
            if A[r][c] != B[r][c]:
                return (r, c, A[r][c], B[r][c])
    return None


def fmt(q):
    return str(q.numerator) if q.denominator == 1 else f'{q.numerator}/{q.denominator}'


fails = 0


def false(name, lhs, rhs):
    global fails
    d = diff(lhs, rhs)
    if d is None:
        print(f'UNEXPECTED: printed {name} holds'); fails += 1
    else:
        r, c, x, y = d
        print(f'printed {name:28} false: entry ({r},{c}) is {fmt(x)} vs {fmt(y)}')


def true(name, lhs, rhs):
    global fails
    if diff(lhs, rhs) is None:
        print(f'        {name:28} holds')
    else:
        print(f'UNEXPECTED: {name} fails'); fails += 1


# The circuits of Section 5.6 for X_[a,a+1] (palindromes, so the order of
# composition does not matter), checked first since the rest uses them.
T = {
    0: prod('X0', 'X1', 'CCX01', 'X1', 'X0'),
    1: prod('X0', 'CCX01', 'CCX02', 'CCX01', 'X0'),
    2: prod('X0', 'CCX01', 'X0'),
    3: prod('X0', 'X2', 'CCX01', 'X0', 'CCX12', 'CCX02', 'CCX12', 'X0', 'CCX01', 'X2', 'X0'),
    4: prod('X1', 'CCX01', 'X1'),
    5: prod('CCX01', 'CCX02', 'CCX01'),
}
for d, m in T.items():
    true(f'5.6: X[{d},{d + 1}] circuit', m, Xab(d, d + 1))

NK = GATES['NK']
K4567 = Kabcd(4, 5, 6, 7)

print('-- Figure 4')
false('(33)', GATES['CCX01'], prod('SW12', 'CCX02', 'SW02'))
true('(33) corrected', GATES['CCX01'], prod('SW12', 'CCX02', 'SW12'))

print('-- Section 5.5')
false('CCX12 = X[6,7]', GATES['CCX12'], Xab(6, 7))
true('CCX01 = X[6,7]', GATES['CCX01'], Xab(6, 7))
true('CCX12 = X[3,7]', GATES['CCX12'], Xab(3, 7))
true('rX', GATES['X0'], prod(Xab(0, 4), Xab(1, 5), Xab(2, 6), Xab(3, 7)))
false('rCX', GATES['CX01'], prod(Xab(2, 6), Xab(3, 7)))
true('rCX corrected: X[4,6] X[5,7]', GATES['CX01'], prod(Xab(4, 6), Xab(5, 7)))
true('X[2,6] X[3,7] is CX10', GATES['CX10'], prod(Xab(2, 6), Xab(3, 7)))
true('K[0,1,2,3] = NK', Kabcd(0, 1, 2, 3), NK)
true('K[4,5,6,7] = X0 NK X0', K4567, prod('X0', NK, 'X0'))
# K[0,1,2,3] acts on the states 0..3, where qubit 0 is |0>.
assert all(NK[r][c] == ID[r][c] for r in range(4, 8) for c in range(8))
true('rK as printed', GATES['K12'], prod(K4567, 'X0', K4567, 'X0'))
true('rK as X0 NK X0 NK', GATES['K12'], prod('X0', NK, 'X0', NK))

print('-- Section 5.6')
false('(-1)[0] = X0 X1 CCZ X1 X0', Mi(0), prod('X0', 'X1', 'CCZ', 'X1', 'X0'))
true('X0 X1 CCZ X1 X0 = (-1)[1]', Mi(1), prod('X0', 'X1', 'CCZ', 'X1', 'X0'))
true('corrected: X0 X1 X2 CCZ ...', Mi(0), prod('X0', 'X1', 'X2', 'CCZ', 'X2', 'X1', 'X0'))

print('-- Figure 7 (and Figures 5, 6, 10)')
false('(97) = (78) = (125)', prod(T[0], NK), prod(NK, T[0], Mi(1), Mi(3)))
true('(97) corrected', prod(T[0], NK), prod(NK, Xab(1, 3), Mi(1), Mi(3)))
false('(100) = (81) = (128)', prod(NK, Kabcd(1, 3, 4, 5)), prod(Kabcd(1, 3, 4, 5), NK))
true('(100) corrected', prod(NK, Kabcd(1, 3, 4, 5)), prod(Kabcd(2, 3, 4, 5), Kabcd(0, 1, 2, 4)))
# The schemas (63) and (66) of Figure 5, at every admissible choice of
# indices: printed false at each one, corrected true at each one.
q4 = list(itertools.combinations(range(8), 4))
assert all(diff(prod(Xab(a, b), Kabcd(a, b, c, d)),
                prod(Kabcd(a, b, c, d), Xab(a, b), Mi(b), Mi(d))) for a, b, c, d in q4)
assert all(not diff(prod(Xab(a, b), Kabcd(a, b, c, d)),
                    prod(Kabcd(a, b, c, d), Xab(b, d), Mi(b), Mi(d))) for a, b, c, d in q4)
print(f'        (63) printed false, corrected true at all {len(q4)} index choices')
q6 = list(itertools.combinations(range(8), 6))
assert all(diff(prod(Kabcd(a, b, c, d), Kabcd(b, d, e, f)),
                prod(Kabcd(b, d, e, f), Kabcd(a, b, c, d))) for a, b, c, d, e, f in q6)
assert all(not diff(prod(Kabcd(a, b, c, d), Kabcd(b, d, e, f)),
                    prod(Kabcd(c, d, e, f), Kabcd(a, b, c, e))) for a, b, c, d, e, f in q6)
print(f'        (66) printed false, corrected true at all {len(q6)} index choices')

print('-- the rest of Figure 7')
rho = prod(K4567, NK, Xab(3, 4), NK, K4567)
true('(101)', prod(Mi(0), Mi(4), Xab(0, 4), rho), prod(rho, Xab(0, 4), Mi(4), Mi(0)))
rho10 = prod(rho, Xab(0, 4))
true('(129) with its own rho', prod(Mi(0), Mi(4), Xab(0, 4), rho10), prod(rho10, Xab(0, 4), Mi(4), Mi(0)))

print('-- Section 5.7')
X56 = Xab(5, 6)
ccz = GATES['CCZ']
for name, word in [('as printed (A o B = A B)', ['K12', 'CZ12', 'X0', NK, 'X0', 'CZ12', NK, X56]),
                   ('reversed (A o B = B A)', [X56, NK, 'CZ12', 'X0', NK, 'X0', 'CZ12', 'K12'])]:
    d = diff(ccz, prod(*word))
    print(f'        CCZ decomposition {name}:', 'holds' if d is None else f'false at {d[:2]}')
kc = prod('K12', 'CCZ')
for name, word in [('as printed (A o B = A B)', [kc, kc, kc, X56]),
                   ('reversed (A o B = B A)', [X56, prod('CCZ', 'K12'), prod('CCZ', 'K12'), prod('CCZ', 'K12')])]:
    d = diff(NK, prod(*word))
    print(f'        K[0,1,2,3] decomposition {name}:', 'holds' if d is None else f'false at {d[:2]}')

print('-- r_K is independent of R1: the model g -> R g R on the Toffoli-K gates')
R = [[ID[r][c] - Fr(1, 4) for c in range(N)] for r in range(N)]
true('R R = I', prod(R, R), ID)
for g in ['X0', 'X1', 'X2', 'CX01', 'CX12', 'CCX01', 'CCX12', 'SW01']:
    assert prod(R, g) == prod(g, R)
lhs = prod(R, 'K12', R)
rhs = prod(prod(R, 'X0', R), NK, prod(R, 'X0', R), NK)
print(f'        (R K12 R)(0,0) = {fmt(lhs[0][0])},  (X0 NK X0 NK)(0,0) = {fmt(rhs[0][0])}')


def intertwiners(pairs):
    """The dimension of the space of 8 x 8 h with h x = y h for (x, y) in pairs."""
    rows = []
    for x, y in pairs:
        for r in range(N):
            for c in range(N):
                row = [Fr(0)] * (N * N)
                for k in range(N):
                    row[N * r + k] += x[k][c]
                    row[N * k + c] -= y[r][k]
                rows.append(row)
    rank = 0
    for col in range(N * N):
        p = next((i for i in range(rank, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[rank], rows[p] = rows[p], rows[rank]
        piv = rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i][col] != 0:
                f = rows[i][col] / piv[col]
                rows[i] = [a - f * b for a, b in zip(rows[i], piv)]
        rank += 1
    return N * N - rank


# Reading H2 as h, (102)-(107) say h x = y h for these pairs (x, y).
def figure8(conj):
    k01, k12 = conj(GATES['K01']), conj(GATES['K12'])
    return [(GATES['X0'], GATES['X0']), (GATES['CX01'], GATES['CX01']),
            (GATES['CCX12'], prod(k01, k12, 'CCZ', k12, k01)),
            (GATES['CCZ'], GATES['CCX01']), (k12, k12), (NK, NK)]


d1 = intertwiners(figure8(lambda g: g))
d2 = intertwiners(figure8(lambda g: prod(R, g, R)))
print(f'        (102)-(107) solvable for h: intended semantics {d1} dimension(s) (h = H2 up to scale),'
      f' the model {d2} (h = 0 only)')
if (d1, d2) != (1, 0):
    print('UNEXPECTED: intertwiner dimensions'); fails += 1

print('FAILURES:', fails)

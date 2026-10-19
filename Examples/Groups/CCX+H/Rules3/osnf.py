"""Smith normal form over O = Z[sqrt2]: pi-exponents of gE_O relative to E_O."""
from fractions import Fraction as F
from snf import basisE
from tree import S

# elements of O as (a, b) ints: a + b sqrt2
def omul(x, y): return (x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def osub(x, y): return (x[0]-y[0], x[1]-y[1])
def onorm(x): return abs(x[0]*x[0] - 2*x[1]*x[1])
def oconj(x): return (x[0], -x[1])
def iszero(x): return x[0] == 0 and x[1] == 0
def odivmod(x, y):
    n = y[0]*y[0] - 2*y[1]*y[1]
    num = omul(x, oconj(y))
    q = (round(F(num[0], n)), round(F(num[1], n)))
    r = osub(x, omul(q, y))
    return q, r
def vpi(x):
    k = 0
    while not iszero(x) and x[0] % 2 == 0:
        x = (x[1], x[0] // 2); k += 1
    return k

def osnf_exps(A):
    """A: square matrix over O (list of rows of (a,b)). Returns pi-valuations of divisors."""
    A = [row[:] for row in A]; n = len(A)
    out = []
    for t in range(n):
        # pivot: min norm nonzero
        def pick():
            best = None
            for i in range(t, n):
                for j in range(t, n):
                    if not iszero(A[i][j]) and (best is None or onorm(A[i][j]) < onorm(A[best[0]][best[1]])):
                        best = (i, j)
            return best
        while True:
            best = pick()
            if best is None:
                return out + [None] * (n - t)
            i, j = best
            A[t], A[i] = A[i], A[t]
            for r in A: r[t], r[j] = r[j], r[t]
            p = A[t][t]
            clean = True
            for i in range(t + 1, n):
                if not iszero(A[i][t]):
                    q, _ = odivmod(A[i][t], p)
                    A[i] = [osub(a, omul(q, b)) for a, b in zip(A[i], A[t])]
                    if not iszero(A[i][t]): clean = False
            for j in range(t + 1, n):
                if not iszero(A[t][j]):
                    q, _ = odivmod(A[t][j], p)
                    for r in A: r[j] = osub(r[j], omul(q, r[t]))
                    if not iszero(A[t][j]): clean = False
            if not clean: continue
            bad = None
            for i in range(t + 1, n):
                for j in range(t + 1, n):
                    _, r = odivmod(A[i][j], p)
                    if not iszero(r): bad = i; break
                if bad is not None: break
            if bad is not None:
                A[t] = [(a[0]+b[0], a[1]+b[1]) for a, b in zip(A[t], A[bad])]
                continue
            break
        out.append(A[t][t])
    return out

_BE = basisE()
def _inv(M):
    n = len(M)
    aug = [M[i][:] + [F(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if aug[r][c] != 0)
        aug[c], aug[p] = aug[p], aug[c]
        pv = aug[c][c]; aug[c] = [x / pv for x in aug[c]]
        for r in range(n):
            if r != c and aug[r][c] != 0:
                f = aug[r][c]; aug[r] = [x - f*y for x, y in zip(aug[r], aug[c])]
    return [row[n:] for row in aug]
_Bt = [list(r) for r in zip(*_BE)]
_Binv = _inv(_Bt)

def exps(Mcols, base=None):
    """pi-exponents of g E_O relative to E_O, g given by scaled columns."""
    # coordinates C = Binv * g * Bt (over Q(sqrt2)); entries as (Fa, Fb)
    n = 8
    gB = []
    for v in _BE:
        w = []
        for i in range(n):
            a = b = F(0)
            for k in range(n):
                ca, cb = Mcols[k][i]
                if v[k]:
                    a += v[k] * ca; b += v[k] * cb
            w.append((a / S, b / S))
        gB.append(w)
    C = [[None]*n for _ in range(n)]
    for j in range(n):  # column j = coords of gB[j]
        for i in range(n):
            a = sum(_Binv[i][k] * gB[j][k][0] for k in range(n))
            b = sum(_Binv[i][k] * gB[j][k][1] for k in range(n))
            C[i][j] = (a, b)
    # scale by 2^s to make integral
    s = 0
    while any((x[0] * 2**s).denominator != 1 or (x[1] * 2**s).denominator != 1 for row in C for x in row):
        s += 1
    A = [[(int(x[0] * 2**s), int(x[1] * 2**s)) for x in row] for row in C]
    ds = osnf_exps(A)
    return sorted(vpi(d) - 2 * s for d in ds)

if __name__ == "__main__":
    from tree import word_matrix
    print("I", exps(word_matrix("")))
    print("H0", exps(word_matrix("H0")))
    print("CCZ", exps(word_matrix("H0 CCX0 H0")))

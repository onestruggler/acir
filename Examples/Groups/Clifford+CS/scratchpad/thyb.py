# The hybrid rules of P' at the matrix level (N indices): the letters,
# the decoding's chains, and the core facts a generic proof of the
# hybrid rules would reduce them to.  Words are read in written order as
# products of matrices left to right.
import sys, itertools
N = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 8
I = 1j

def eye():
    return [[1 if r == c else 0 for c in range(N)] for r in range(N)]
def mul(A, B):
    return [[sum(A[r][k] * B[k][c] for k in range(N) if A[r][k] != 0) for c in range(N)] for r in range(N)]
def close(A, B): return all(abs(A[r][c] - B[r][c]) < 1e-9 for r in range(N) for c in range(N))
def diag(d):
    M = eye()
    for k, v in d.items(): M[k][k] = v
    return M

def pp(a, b):
    if a == b: return eye()
    return diag({a: I, b: -I})
def isink(s): return diag({s: -I})                     # i_s^-1
def neg(c): return diag({c: -1})
def X(a, b):
    M = eye(); M[a][a] = M[b][b] = 0; M[a][b] = M[b][a] = 1; return M
def px(c, a, b): return mul(neg(c), X(a, b))
def K(a, b):
    g = 1 / (1 + I)
    M = eye(); M[a][a] = g; M[a][b] = g; M[b][a] = g; M[b][b] = -g; return M
def ki(a, b, s): return mul(K(a, b), isink(s))

def word(*ms):
    M = eye()
    for m in ms: M = mul(M, m)
    return M

# the consecutive letters
def p(a): return pp(a, a + 1)
def pq(a): return pp(a + 1, a)
def l(a): return px(a, a, a + 1)
def h(a): return px(a + 1, a, a + 1)
def k(a): return ki(a, a + 1, a)

def dKIa(a, d):
    if d == 1: return k(a)
    return word(h(a), dKIa(a + 1, d - 1), l(a))
def dLo(a, d):
    if d == 1: return l(a)
    return word(h(a), dLo(a + 1, d - 1), l(a))

def check(name, A, B):
    ok = close(A, B)
    if not ok: print('FAIL', name)
    return ok

if __name__ == '__main__':
    bad = 0
    # the decoding's chains denote their letters
    for a in range(N):
        for b in range(a + 1, N):
            bad += not check(f'dKIa {a} {b}', dKIa(a, b - a), ki(a, b, a))
            bad += not check(f'dLo {a} {b}', dLo(a, b - a), px(a, a, b))
    # the rules of Auxiliary/Rules hold in this convention
    rng = range(N)
    for a, b, s in itertools.product(rng, rng, rng):
        if not (a < b) or s in (a, b): continue
        bad += not check('ki-x', word(ki(a, b, s), pp(b, s), pp(b, s)), word(px(s, a, b), ki(a, b, s)))
        bad += not check('ki-16', word(ki(a, b, s), pp(b, s), pp(b, s), pp(b, s)),
                         word(pp(b, s), ki(a, b, s), pp(b, s), ki(a, b, s)))
        bad += not check('ki-ii', word(ki(a, b, s), pp(a, s), pp(b, s)), word(pp(a, s), pp(b, s), ki(a, b, s)))
        bad += not check('ki-sq', word(ki(a, b, s), ki(a, b, s), pp(a, s), pp(b, s)), eye())
    print('bad', bad)

def dPP(a, b):
    if a < b: return word(*[p(j) for j in range(a, b)])
    return word(*[pq(j) for j in range(b, a)])
def comm(A, B): return close(mul(A, B), mul(B, A))

if __name__ == '__main__' and 'facts' in sys.argv:
    res = {}
    def rec(name, ok): res.setdefault(name, []).append(ok)
    for c in range(N - 1):
        for j in range(N - 1):
            if abs(j - c) >= 2:
                rec('kp-far', comm(k(c), p(j))); rec('kl-far', comm(k(c), l(j))); rec('kk-far', comm(k(c), k(j)))
        if c >= 1 and c + 2 < N:
            rec('kp-bridge', comm(k(c), dPP(c - 1, c + 2)))
            rec('kl-bridge', comm(k(c), dLo(c - 1, 3)))
            rec('kk-bridge', comm(k(c), dKIa(c - 1, 3)))
        for x in range(N):
            if x in (c, c + 1): continue
            rec('scalar', comm(k(c), word(dPP(c, x), dPP(c + 1, x))))
            rec('scalar-anti', comm(k(c), word(dPP(c, x), dPP(x, c + 1))))
    for kname, v in res.items(): print(kname, sum(v), '/', len(v))

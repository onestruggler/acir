# An exact mirror of the list computations of Sym.lean, SymState.lean, SymSplit.lean,
# SymNode.lean, SymClean.lean and Case34Base.lean, so that every `decide` emitted by
# gen_case34.py is known to succeed.  Letters: ('Z', p), ('X', p, q), ('H', p, q) with p < q.
# Words are in written order (the rightmost letter acts first).  Forms are lists of ints,
# the constant first; an entry is a pair (rational part, sqrt2 part).

dZ = ([], [])

def ladd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]

def lsmul(c, l): return [c * x for x in l]
def allEven(l): return all(x % 2 == 0 for x in l)
def lhalf(l): return [x // 2 for x in l]
def zadd(x, y): return (ladd(x[0], y[0]), ladd(x[1], y[1]))
def zneg(x): return (lsmul(-1, x[0]), lsmul(-1, x[1]))
def zsub(x, y): return zadd(x, zneg(y))
def zrt2(x): return (lsmul(2, x[1]), list(x[0]))

def zdiv(x):
    return (list(x[1]), lhalf(x[0])) if allEven(x[0]) else None

def zdivp(h, x):
    for _ in range(h):
        if x is None: return None
        x = zdiv(x)
    return x

def getD(P, j): return P[j] if j < len(P) else dZ

def scgE(g, P, j):
    if g[0] == 'Z':
        return zneg(getD(P, j)) if j == g[1] else getD(P, j)
    p, q = g[1], g[2]
    if g[0] == 'X':
        return getD(P, q) if j == p else (getD(P, p) if j == q else getD(P, j))
    if j == p: return zadd(getD(P, p), getD(P, q))
    if j == q: return zsub(getD(P, p), getD(P, q))
    return zrt2(getD(P, j))

def scgL(g, P, w): return [scgE(g, P, j) for j in range(w)]

def scwL(ws, P, w):
    for g in reversed(ws): P = scgL(g, P, w)
    return P

def hcntw(ws): return sum(1 for g in ws if g[0] == 'H')

def divAt(P, ws, j, w): return zdivp(hcntw(ws), getD(scwL(ws, P, w), j))
def divAll(P, ws, w):
    out = []
    for j in range(w):
        y = divAt(P, ws, j, w)
        out.append(dZ if y is None else y)
    return out
def allSome(P, ws, w): return all(divAt(P, ws, j, w) is not None for j in range(w))

def oddSure(x): return len(x[0]) > 0 and x[0][0] % 2 == 1 and allEven(x[0][1:])
def oddSureL(l): return len(l) > 0 and l[0] % 2 == 1 and allEven(l[1:])

def maybeOdd(P, ws, j, w):
    y = divAt(P, ws, j, w)
    return True if y is None else not allEven(y[0])

def stOK(P, ws, w):
    if not allSome(P, ws, w): return False
    return (sum(1 for j in range(w) if maybeOdd(P, ws, j, w)) <
            sum(1 for j in range(w) if oddSure(getD(P, j))))

def pathOK(P, D, A, w): return all(stOK(P, list(D[k:]) + list(A), w) for k in range(len(D) + 1))

def sameOdd(P, P2, w):
    return all((oddSure(getD(P, j)) and oddSure(getD(P2, j))) or
               (allEven(getD(P, j)[0]) and allEven(getD(P2, j)[0])) for j in range(w))

def divAtD(P, ws, d, j, w): return zdivp(hcntw(ws) + d, getD(scwL(ws, P, w), j))
def divAllD(P, ws, d, w):
    out = []
    for j in range(w):
        y = divAtD(P, ws, d, j, w)
        out.append(dZ if y is None else y)
    return out
def allSomeD(P, ws, d, w): return all(divAtD(P, ws, d, j, w) is not None for j in range(w))

def isCls(g, x): return oddSure(x) and (oddSureL(x[1]) if g else allEven(x[1]))
def notCls(g, x):
    return allEven(x[0]) or (oddSure(x) and (allEven(x[1]) if g else oddSureL(x[1])))
def clsCount(V, g, par, w):
    return (all(isCls(g, getD(V, j)) or notCls(g, getD(V, j)) for j in range(w)) and
            sum(1 for j in range(w) if isCls(g, getD(V, j))) % 2 == par)

def sumRe(V, w):
    acc = []
    for j in reversed(range(w)): acc = ladd(getD(V, j)[0], acc)
    return acc

def Pwidth(P, nv): return all(len(x[0]) <= nv + 1 and len(x[1]) <= nv + 1 for x in P)

def lnorm(l):
    l = list(l)
    while l and l[-1] == 0: l.pop()
    return l
def Pnorm(P): return [(lnorm(x[0]), lnorm(x[1])) for x in P]

def sumL(cs, phi):
    if not cs or not phi: return []
    return ladd(lsmul(cs[0], phi[0]), sumL(cs[1:], phi[1:]))
def substL(l, phi): return [] if not l else ladd([l[0]], sumL(l[1:], phi))
def Psubst(P, phi): return [(substL(x[0], phi), substL(x[1], phi)) for x in P]

def ivar(i): return [0] + [0] * i + [1]
def splitphi(nv, v, L): return [L if i == v else ivar(i) for i in range(nv)]
def lget(l, i): return l[i] if i < len(l) else 0
def lset(l, i, b):
    l = list(l)
    if i < len(l): l[i] = b
    return l
def lmod2(l): return [x % 2 for x in l]
def splitR(lf, p): return lset(lmod2(lf[1:]), p, 0)
def splitL(lf, p, b):
    head = lf[0] if lf else 0
    return [(b - head) % 2] + lset(lsmul(-1, splitR(lf, p)), p, 2)

def dbase(g, nv): return ([1] + [0] * nv + [2, 0], [1 if g else 0] + [0] * nv + [0, 2])
def dent(d, g, nv):
    x = dbase(g, nv)
    for _ in range(d): x = zrt2(x)
    return x
def Pext2(P, d, g, nv): return list(P) + [dent(d, g, nv), dent(d, g, nv + 2)]

def cleanStepOK(P, nv, d, A0, B0, g, w):
    P2 = Pext2(P, d, g, nv)
    K = [('H', w, w + 1)]
    W2 = w + 2
    V = divAll(P2, K, W2)
    return (allSome(P2, K, W2) and oddSure(getD(V, 0)) and sameOdd(P2, V, W2) and
            pathOK(P2, K, A0, W2) and pathOK(P2, K, B0, W2) and
            Pnorm(V[:w]) == Pnorm(P) and
            zdivp(d + 1, getD(V, w)) is not None and zdivp(d + 1, getD(V, w + 1)) is not None)

def cleanOK(P, nv, d, D, A0, B0, w):
    return (Pwidth(P, nv) and len(P) == w and 0 < w and allSomeD(P, D, d, w) and
            clsCount(divAllD(P, D, d, w), False, 0, w) and
            clsCount(divAllD(P, D, d, w), True, 0, w) and
            cleanStepOK(P, nv, d, A0, B0, False, w) and cleanStepOK(P, nv, d, A0, B0, True, w))

def tailDiv(P, w, w2): return all(zdivp(1, getD(P, w + j)) is not None for j in range(w2 - w))

def disjW(A, K):
    def idx(g): return [g[1]] if g[0] == 'Z' else [g[1], g[2]]
    return all(i != i2 for g in A for g2 in K for i in idx(g) for i2 in idx(g2))

def countOddSure(V, w): return sum(1 for j in range(w) if oddSure(getD(V, j)))

# ---- evaluation, for testing ----
def ev(l, t):
    return (l[0] if l else 0) + sum(c * t[i] for i, c in enumerate(l[1:]))

def zevals(P, t): return [(ev(x[0], t), ev(x[1], t)) for x in P]

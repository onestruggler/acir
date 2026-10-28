"""Refactoring  sigma K_S tau  into  sigma' K_S' tau'  by Table 1 / macro steps.

Signed permutations are tuples img with img[j] = s*(p+1): e_j -> s e_p.
A word x1 x2 ... xk has the map x1 o x2 o ... o xk (matrix product)."""
from collections import deque
from rules import N, X, K
from sides2 import apply_all
from sptools import sp_derive

def sp_of_gen(g, m):
    img = list(range(1, m + 1))
    if g[0] == 'n':
        img[g[1]] = -(g[1] + 1)
    else:
        a, b = g[1], g[2]
        img[a], img[b] = b + 1, a + 1
    return tuple(img)

def comp(A, B):
    """A o B."""
    out = []
    for v in B:
        p, s = abs(v) - 1, (1 if v > 0 else -1)
        w = A[p]
        out.append(s * w)
    return tuple(out)

def ident(m):
    return tuple(range(1, m + 1))

def sp_of_word(w, m):
    r = ident(m)
    for g in w:
        r = comp(r, sp_of_gen(g, m))
    return r

def inv(A):
    out = [0] * len(A)
    for j, v in enumerate(A):
        p, s = abs(v) - 1, (1 if v > 0 else -1)
        out[p] = s * (j + 1)
    return tuple(out)

def word_of_sp(A):
    """A canonical word (transpositions then signs) for A."""
    m = len(A)
    pi = [abs(v) - 1 for v in A]
    sg = [1 if v > 0 else -1 for v in A]
    trans = []
    cur = list(pi)
    while True:
        bad = [j for j in range(m) if cur[j] != j]
        if not bad:
            break
        j = bad[0]
        i = cur[j]
        a, b = min(i, j), max(i, j)
        trans.append(X(a, b))
        cur = [(b if x == a else a if x == b else x) for x in cur]
    w = tuple(trans) + tuple(N(j) for j in range(m) if sg[j] == -1)
    assert sp_of_word(w, m) == A
    return w

POS_X = {(0, 1): ('r4a', lambda S: (X(S[1], S[3]), N(S[1]), N(S[3]))),
         (1, 2): ('ksym2', lambda S: (X(S[1], S[2]),)),
         (2, 3): ('r4c', lambda S: (X(S[1], S[3]),)),
         (0, 2): ('ksym4', lambda S: (X(S[2], S[3]), N(S[2]), N(S[3]))),
         (0, 3): ('ksym5', lambda S: (X(S[1], S[3]), X(S[2], S[3]), X(S[1], S[3]), N(S[1]), N(S[2]))),
         (1, 3): ('ksym6', lambda S: (X(S[2], S[3]),))}
POS_N = {(0, 1): ('k12', lambda S: (X(S[0], S[2]), X(S[1], S[3]), N(S[0]), N(S[1]), N(S[2]), N(S[3]))),
         (0, 2): ('k22', lambda S: (X(S[0], S[1]), X(S[2], S[3]), N(S[0]), N(S[1]), N(S[2]), N(S[3]))),
         (0, 3): ('k32', lambda S: (X(S[0], S[3]), X(S[1], S[2]), N(S[0]), N(S[1]), N(S[2]), N(S[3]))),
         (1, 2): ('k31', lambda S: (X(S[0], S[3]), X(S[1], S[2]))),
         (1, 3): ('k21', lambda S: (X(S[0], S[1]), X(S[2], S[3]))),
         (2, 3): ('k11', lambda S: (X(S[0], S[2]), X(S[1], S[3])))}
REN = ['r3d', 'r3e', 'r3f', 'r3g']

def moves(S, m):
    """Generators x (as words) passing K_S: (x, step(fam, ps, dir), S', y)."""
    S = tuple(S)
    out = []
    for i in range(m):
        if i not in S:
            out.append(((N(i),), ('r2e', [i] + list(S), True), S, (N(i),)))
    for i in range(m):
        for j in range(i + 1, m):
            if i not in S and j not in S:
                out.append(((X(i, j),), ('r2c', [i, j] + list(S), True), S, (X(i, j),)))
            elif i in S and j in S:
                p, q = S.index(i), S.index(j)
                fam, y = POS_X[(p, q)]
                out.append(((X(i, j),), (fam, list(S), True), S, y(S)))
                fam, y = POS_N[(p, q)]
                out.append(((N(i), N(j)), (fam, list(S), True), S, y(S)))
            elif i in S:          # lo in S, rename to hi
                p = S.index(i)
                if p == 3 or S[p + 1] > j:
                    S2 = tuple(sorted(set(S) - {i} | {j}))
                    ps = list(S[:p]) + [i, j] + list(S[p + 1:])
                    out.append(((X(i, j),), (REN[p], ps, True), S2, (X(i, j),)))
            else:                 # hi = j in S, rename to lo = i
                p = S.index(j)
                if p == 0 or S[p - 1] < i:
                    S2 = tuple(sorted(set(S) - {j} | {i}))
                    ps = list(S[:p]) + [i, j] + list(S[p + 1:])
                    out.append(((X(i, j),), ('rev_' + REN[p], ps, False), S2, (X(i, j),)))
    return out

_mv = {}
def pass_plan(rho, S, S_target, m):
    """Words x1..xk with rho = x1...xk, passing K_S successively to K_{S_target}.
    Returns list of (x, step, S_before, S_after, y) in order of application (xk first)."""
    start = (rho, tuple(S))
    goal = (ident(m), tuple(S_target))
    if start == goal:
        return []
    par = {start: None}
    dq = deque([start])
    while dq:
        st = dq.popleft()
        r, Sc = st
        if Sc not in _mv:
            _mv[Sc] = moves(Sc, m)
        for x, step, S2, y in _mv[Sc]:
            r2 = comp(r, sp_of_word(x, m))   # r = r2 . x  =>  r2 = r . x^-1 = r . x
            nst = (r2, S2)
            if nst in par:
                continue
            par[nst] = (st, x, step, Sc, S2, y)
            if nst == goal:
                plan = []
                cur = nst
                while par[cur] is not None:
                    prev, x, step, Sc, S2, y = par[cur]
                    plan.append((x, step, Sc, S2, y))
                    cur = prev
                return plan          # plan[0] = leftmost x1, plan[-1] = xk (passed first)
            dq.append(nst)
    return None

def refactor(w, i0, kpos, i1, sig2, S2, tau2, m):
    """w[i0:kpos] = sigma (sp), w[kpos] = K_S, w[kpos+1:i1] = tau (sp).
    Rewrite into sig2 K_S2 tau2 (words).  Returns (steps, new word)."""
    w = tuple(w)
    sigma, tau = w[i0:kpos], w[kpos + 1:i1]
    S = w[kpos][1:]
    rho = comp(inv(sp_of_word(sig2, m)), sp_of_word(sigma, m))
    plan = pass_plan(rho, S, S2, m)
    assert plan is not None, ('no pass plan', S, S2)
    xs = []
    for x, step, Sc, Sn, y in plan:
        xs += list(x)
    steps = []
    # left gap: sigma -> sig2 + xs
    st = sp_derive(sigma, tuple(sig2) + tuple(xs), m, off=i0)
    steps += st
    cur = w[:i0] + tuple(sig2) + tuple(xs) + w[kpos:]
    kp = i0 + len(sig2) + len(xs)
    ys = ()
    for x, step, Sc, Sn, y in reversed(plan):
        fam, ps, d = step
        pos = kp - len(x)
        steps.append((fam, ps, d, pos))
        cur = apply_all(cur, [(fam, ps, d, pos)])
        kp = pos
        ys = tuple(y) + ys
    # now cur = w[:i0] + sig2 + K_S2 + ys + tau + w[i1:]
    kp = i0 + len(sig2)
    assert cur[kp] == K(*S2), (cur, kp, S2)
    st2 = sp_derive(ys + tuple(tau), tuple(tau2), m, off=kp + 1)
    steps += st2
    new = w[:i0] + tuple(sig2) + (K(*S2),) + tuple(tau2) + w[i1:]
    assert apply_all(w, steps) == new
    return steps, new

import numpy as np, itertools
s = 1/np.sqrt(2)

def Zm(N, a):
    M = np.eye(N); M[a, a] = -1; return M
def Xm(N, a, b):
    M = np.eye(N); M[a, a] = M[b, b] = 0; M[a, b] = M[b, a] = 1; return M
def Hm(N, a, b):
    # H_[a,b]: first row/col at a: [[s, s],[s,-s]] on (a,b)
    M = np.eye(N); M[a, a] = s; M[a, b] = s; M[b, a] = s; M[b, b] = -s; return M

def gmat(N, g):
    k = g[0]
    if k == 'Z': return Zm(N, g[1])
    if k == 'X': return Xm(N, g[1], g[2])
    if k == 'H': return Hm(N, g[1], g[2])
    if k == 'zz': return Zm(N, g[1]) @ Zm(N, g[2])
    if k == 'zx': return Zm(N, g[1]) @ Xm(N, g[2], g[3])
    if k == 'xx': return Xm(N, g[1], g[2]) @ Xm(N, g[3], g[4])
    if k == 'hh': return Hm(N, g[1], g[2]) @ Hm(N, g[3], g[4])
    raise ValueError(g)

def wmat(N, w):
    M = np.eye(N)
    for g in w: M = M @ gmat(N, g)
    return M

def eq(N, u, v):
    return np.allclose(wmat(N, u), wmat(N, v))

def supp(w):
    S = set()
    for g in w: S.update(g[1:])
    return S

# Clement words -> Fig6 words (tr)
def tr(w):
    out = []
    for g in w:
        if g[0] == 'Z': out.append(g)
        else:
            a, b = g[1], g[2]
            if a < b: out.append(g)
            else:
                out += [('X', b, a), (g[0], b, a), ('X', b, a)] if g[0] == 'H' else [('X', b, a)]
    return out

def plus(a, b): return b if a == 0 else a
def ab(a, b): return b if a == 1 else a

def tau(c, g):
    k = g[0]
    if c == 'e':
        if k == 'Z': return [('zz', 1, g[1])], 'z'
        if k == 'X':
            a, b = g[1], g[2]
            if a == 1 or b == 1: return [('zx', ab(a, b), a, b)], 'z'
            return [('zx', 1, a, b)], 'z'
        if k == 'H': return [('hh', g[1], g[2], 0, 1)], 'h'
    if c == 'z':
        if k == 'Z': return [('zz', 1, g[1])], 'e'
        if k == 'X': return [('zx', 1, g[1], g[2])], 'e'
        if k == 'H':
            a, b = g[1], g[2]
            if a == 1 or b == 1: return [('zx', b, a, b), ('hh', a, b, 0, 1)], 'hz'
            return [('hh', a, b, 0, 1)], 'hz'
    if c in ('h', 'hz'):
        nxt = {'h': 'hz', 'hz': 'h'}[c]
        if k == 'Z':
            a = g[1]
            if a in (0, 1): return [('zz', 1, a)], nxt
            return [('zx', a, 0, 1)], nxt
        if k == 'X':
            a, b = g[1], g[2]; S = {a, b} & {0, 1}
            if S == {0, 1}: return [('zx', 1 if c == 'h' else 0, 0, 1)], nxt
            if S == {0}: return [('xx', 0, 1, a, b), ('hh', plus(a, b), 1, 0, 1)], nxt
            if S == {1}:
                if c == 'h': return [('zx', ab(a, b), a, b), ('hh', 0, ab(a, b), 0, 1)], nxt
                return [('xx', 0, 1, a, b), ('hh', 0, ab(a, b), 0, 1)], nxt
            return [('xx', a, b, 0, 1)], nxt
        if k == 'H':
            a, b = g[1], g[2]
            if c == 'h': return [('hh', 0, 1, a, b)], 'e'
            if a == 1 or b == 1: return [('hh', 0, 1, a, b), ('zx', a, a, b)], 'z'
            return [('hh', 0, 1, a, b)], 'z'

def tstar(c, w):
    out = []
    for g in w:
        p, c = tau(c, g); out += p
    return out, c

def ren(rho, w):
    return [(g[0],) + tuple(rho[i] for i in g[1:]) for g in w]

# Fig8 (45), (46)
L45 = [('hh', 0, 1, 7, 6), ('hh', 0, 3, 1, 2), ('hh', 0, 1, 7, 6), ('zz', 0, 1), ('hh', 0, 3, 1, 2)]
R45 = [('hh', 0, 3, 1, 2), ('zz', 0, 1), ('hh', 0, 1, 7, 6), ('hh', 0, 3, 1, 2), ('hh', 0, 1, 7, 6)]
L46 = [('hh', 0, 1, 7, 6), ('hh', 0, 3, 1, 2), ('hh', 3, 4, 2, 5), ('hh', 3, 2, 4, 5), ('hh', 7, 6, 4, 5),
       ('zz', 2, 3), ('hh', 3, 4, 2, 5), ('hh', 0, 3, 1, 2)]
R46 = [('hh', 0, 3, 1, 2), ('hh', 3, 4, 2, 5), ('zz', 2, 3), ('hh', 7, 6, 4, 5), ('hh', 3, 2, 4, 5),
       ('hh', 3, 4, 2, 5), ('hh', 0, 3, 1, 2), ('hh', 0, 1, 7, 6)]

def H(a, b): return ('H', a, b)
def Z(a): return ('Z', a)
def X(a, b): return ('X', a, b)

# Clement (20), (21) at template indices
L20 = [H(0,1), H(0,2), H(1,3), H(0,1), Z(0), Z(1), H(0,2), H(1,3)]
R20 = [H(0,2), H(1,3), H(0,1), Z(0), Z(1), H(0,2), H(1,3), H(0,1)]
L21 = [H(0,1), H(0,2), H(1,3), H(0,4), H(1,5), H(0,1), Z(0), Z(1), H(0,4), H(1,5), H(0,2), H(1,3)]
R21 = [H(0,2), H(1,3), H(0,4), H(1,5), H(0,1), Z(0), Z(1), H(0,4), H(1,5), H(0,2), H(1,3), H(0,1)]
# (d3) at (a,b,c,d): (H_cd H_ac H_bd)^4 = H_ab H_cd
def d3(a, b, c, d): return [H(c, d), H(a, c), H(b, d)] * 4, [H(a, b), H(c, d)]
def d4(a, b, c, d, e, f):
    blk = [H(a, c), H(b, d), H(a, b), H(a, c), H(b, d), X(c, e), X(d, f)]
    return blk * 3, [H(c, e), H(d, f), H(e, f), H(c, e), H(d, f), X(c, e), X(d, f)]

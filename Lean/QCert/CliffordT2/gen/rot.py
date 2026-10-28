# Pauli rotation normal forms (semantic prototype).
# A Clifford+T word is brought to C . R(P1) ... R(Pn), C Clifford, Pi positive Paulis,
# canonical up to commutation (bubble sort by a fixed order).
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from collections import deque
from ct import MAT, mat, EQN, AX

PX = np.array([[0,1],[1,0]]); PY = np.array([[0,-1j],[1j,0]]); PZ = np.diag([1,-1]); PI = np.eye(2)
P1 = {'I': PI, 'X': PX, 'Y': PY, 'Z': PZ}
PAULIS = [(s, a + b) for s in (1, -1) for a in 'IXYZ' for b in 'IXYZ' if a + b != 'II']
def pmat(p):
    s, ab = p
    return s * np.kron(P1[ab[0]], P1[ab[1]])
def ident(M):
    for p in PAULIS:
        if np.allclose(M, pmat(p)): return p
    raise ValueError
def conj(C, p):
    """C p C^dagger"""
    return ident(C @ pmat(p) @ C.conj().T)
def conj_inv(C, p):
    """C^dagger p C"""
    return ident(C.conj().T @ pmat(p) @ C)
def commute(p, q):
    A, B = pmat(p), pmat(q)
    return np.allclose(A @ B, B @ A)
ORDER = {ab: i for i, ab in enumerate([a + b for a in 'IXYZ' for b in 'IXYZ' if a + b != 'II'])}

CLIFF = 'wHhSsZ'
INV = {'w': 'w' * 7, 'S': 'SSS', 's': 'sss', 'H': 'H', 'h': 'h', 'Z': 'Z'}
def inv(w): return ''.join(INV[c] for c in reversed(w))

def bfs_cw():
    """Minimal Clifford words cw with cw Z0 cw^dagger = P, built by prepending."""
    start = (1, 'ZI')
    cw = {start: ''}
    q = deque([start])
    while q:
        p = q.popleft()
        for g in CLIFF:
            np_ = conj(MAT[g], p)
            if np_ not in cw:
                cw[np_] = g + cw[p]; q.append(np_)
    return cw
CW = bfs_cw()
def rw(p):
    return CW[p] + 'T' + inv(CW[p])

def raw(word):
    """word -> (C matrix, list of Paulis) with word = C R(P1)...R(Pn)."""
    C = np.eye(4, dtype=complex); rots = []
    for x in word:
        if x in CLIFF:
            rots = [conj_inv(MAT[x], p) for p in rots]
            C = C @ MAT[x]
        elif x == 'T':
            rots.append((1, 'ZI'))
        elif x == 't':
            rots.append((1, 'IZ'))
    return C, rots

def Rmat(p):
    w8 = np.exp(1j * np.pi / 4)
    return (1 + w8) / 2 * np.eye(4) + (1 - w8) / 2 * pmat(p)

def Emat(p):   # R(-p) = E(p) R(p)
    return Rmat((-p[0], p[1])) @ np.linalg.inv(Rmat(p))
def Fmat(p):   # R(p) R(p)
    return Rmat(p) @ Rmat(p)

def canon(word):
    C, rots = raw(word)
    suffix = []
    i = len(rots) - 1
    while i >= 0:
        p = rots[i]
        if p[0] < 0:
            E = Emat((1, p[1]))
            # R(-p) = E R(p); E moves left: conjugates rots[0..i-1], absorbed in C
            rots[:i] = [conj_inv(E, q) for q in rots[:i]]
            C = C @ E
            p = (1, p[1])
        suffix.insert(0, p)
        # bubble sort / merge until stable
        changed = True
        while changed:
            changed = False
            for j in range(len(suffix) - 1):
                a, b = suffix[j], suffix[j + 1]
                if a == b:
                    F = Fmat(a)
                    # F moves left through suffix[0..j-1] (they need not commute!)
                    suffix[:j] = [conj_inv(F, q) for q in suffix[:j]]
                    rots[:i] = [conj_inv(F, q) for q in rots[:i]]
                    C = C @ F
                    del suffix[j:j + 2]
                    changed = True; break
                if commute(a, b) and ORDER[a[1]] > ORDER[b[1]]:
                    suffix[j], suffix[j + 1] = b, a
                    changed = True; break
            if changed and any(q[0] < 0 for q in suffix):
                # a Clifford passed through the suffix and flipped a sign: restart that part
                k = max(j for j, q in enumerate(suffix) if q[0] < 0)
                # move suffix[0..k] back into rots to be reprocessed
                rots = rots[:i] + suffix[:k + 1]
                suffix = suffix[k + 1:]
                i = len(rots)
                break
        i -= 1
    return C, suffix

def check(word):
    C, s = canon(word)
    M = C.copy()
    for p in s: M = M @ Rmat(p)
    return np.allclose(M, mat(word))

if __name__ == '__main__':
    import itertools
    bad = []
    for n, (l, r) in EQN.items():
        assert check(l) and check(r)
        Cl, sl = canon(l); Cr, sr = canon(r)
        same = sl == sr and np.allclose(Cl, Cr)
        print(n, len(sl), len(sr), 'same' if same else 'DIFF', sl if not same else '', sr if not same else '')

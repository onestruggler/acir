# Per-wire gate-count invariants at width 4: the lattice spanned by the
# differences of (#S_w, #K_w, #CS_(w,w+1), #iI) between the two sides of
# every rule instance (each rule at every shift), in the Agda spellings.
import sys; sys.path.insert(0, 'four')
from mac import S, K, CS, I, X, CX01, CX10, SWAP, CCZ0, TOFF0, lift, word_of, mac_tree
from fractions import Fraction
def feat(word):
    v = [0] * 12
    for g, s in word:
        if g == 'S': v[s] += 1
        elif g == 'K': v[4 + s] += 1
        elif g == 'CS': v[8 + s] += 1
        elif g == 'iI': v[11] += 1
    return v
def Z(w): return S(w) + S(w)
R = {   # (width, lhs, rhs) at shift 0
 'order-I': (0, I * 4, []), 'order-S': (1, S(0) * 4, []), 'order-K': (1, K(0) * 2, I * 3),
 'order-SK': (1, (S(0) + K(0)) * 3, I * 3), 'order-CS': (2, CS(0) * 4, []),
 'comm-CS-S0': (2, CS(0) + S(0), S(0) + CS(0)), 'X-CS0': (2, X(0) + CS(0), CS(0) * 3 + X(0) + S(1)),
 'X-CS1': (2, X(1) + CS(0), CS(0) * 3 + X(1) + S(0)),
 'CS-K0': (2, CS(0) + K(0) + CS(0) + K(0) + S(0), S(0) + K(0) + CS(0) + K(0) + CS(0)),
 'rel-266': (3, CX10(0) + CX01(0) + CS(1) + CX01(0) + CX10(0), CX01(1) + CX10(1) + CS(0) + CX10(1) + CX01(1)),
 'rel-267': (3, CX10(0) + CX01(0) + CS(1) * 2 + CX01(0) + CX10(0), CX01(0) + CS(1) * 2 + CX01(0) + CS(1) * 2),
 'rel-268': (3, CS(1) + CX01(0) + CS(1) * 3 + CX01(0), CS(0) + CX10(1) + CS(0) * 3 + CX10(1)),
 'rel-269': (3, CS(1) + K(1) + CS(1) + K(1) + CS(0) + K(1) + CS(0), CS(0) + K(1) + CS(0) + K(1) + CS(1) + K(1) + CS(1)),
 'rel-272': (3, CS(1) + K(1) + CS(1) * 3 + K(1) + CS(0) + K(1) + CS(1), CS(0) + K(1) + CS(0) * 3 + K(1) + CS(1) + K(1) + CS(0)),
 'cx-ccz': (4, lift(CX10(0), 2) + CCZ0 + lift(CX10(0), 2), CCZ0 + SWAP(2) + CCZ0 + SWAP(2)),
 'toff-ccz': (4, TOFF0 + SWAP(2) + CCZ0 + SWAP(2) + TOFF0, SWAP(2) + CCZ0 + SWAP(2) + lift(CCZ0, 1)),
}
def diffs(names):
    out = []
    for nm in names:
        w, l, r = R[nm]
        for j in range(0, 4 - w + 1 if w > 0 else 1):
            out.append([a - b for a, b in zip(feat(lift(l, j)), feat(lift(r, j)))])
    return out
def rank_and_index(rows):
    """Smith-style: rank and the product of the invariant factors."""
    import copy
    M = [list(r) for r in rows if any(r)]
    m, n = len(M), 12
    # integer row/column reduction to diagonal form
    r = 0; diag = []
    cols = list(range(n))
    while True:
        nz = [(abs(M[i][j]), i, j) for i in range(r, len(M)) for j in range(r, n) if M[i][j] != 0]
        if not nz: break
        _, pi, pj = min(nz)
        M[r], M[pi] = M[pi], M[r]
        for row in M: row[r], row[pj] = row[pj], row[r]
        done = False
        while not done:
            done = True
            for i in range(len(M)):
                if i != r and M[i][r] != 0:
                    q = M[i][r] // M[r][r]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r])]
                    if M[i][r] != 0:
                        M[r], M[i] = M[i], M[r]; done = False
            for j in range(n):
                if j != r and M[r][j] != 0:
                    q = M[r][j] // M[r][r]
                    for row in M: row[j] -= q * row[r]
                    if M[r][j] != 0:
                        for row in M: row[r], row[j] = row[j], row[r]
                        done = False
        diag.append(abs(M[r][r])); r += 1
    return r, diag
names = list(R)
rk, d = rank_and_index(diffs(names))
print('rank', rk, 'of 12; invariant factors', [x for x in d if x != 1] or 'all 1')
rk3, d3 = rank_and_index(diffs([n for n in names if n not in ('cx-ccz', 'toff-ccz')]))
print('without the four-wire rules: rank', rk3, 'factors', [x for x in d3 if x != 1] or 'all 1')

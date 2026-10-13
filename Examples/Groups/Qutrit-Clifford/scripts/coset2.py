"""Right cosets L·g of the local subgroup L in the two-qutrit Clifford
group.  Words are strings in operator order (Agda's): letters n h s H S c
(h, s on wire 0; H, S on wire 1; c = CZ)."""
from qt import mat, P

TOK = {'n': ('nu',), 'h': ('H', 0), 's': ('S', 0), 'H': ('H', 1), 'S': ('S', 1), 'c': ('CZ', 0)}

def opmat(word, n=2):
    return mat([TOK[ch] for ch in reversed(word)], n)

def inv(M):
    n = len(M)
    A = [list(r) + [1 if i == j else 0 for j in range(n)] for i, r in enumerate(M)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] % P)
        A[col], A[piv] = A[piv], A[col]
        iv = pow(A[col][col], P - 2, P)
        A[col] = [(x * iv) % P for x in A[col]]
        for r in range(n):
            if r != col and A[r][col]:
                f = A[r][col]
                A[r] = [(x - f * y) % P for x, y in zip(A[r], A[col])]
    return [r[n:] for r in A]

def mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) % P for j in range(n)] for i in range(n)]

def rank(M):
    A = [list(r) for r in M]
    rk = 0; rows = len(A); cols = len(A[0])
    for col in range(cols):
        piv = next((r for r in range(rk, rows) if A[r][col] % P), None)
        if piv is None: continue
        A[rk], A[piv] = A[piv], A[rk]
        iv = pow(A[rk][col], P - 2, P)
        A[rk] = [(x * iv) % P for x in A[rk]]
        for r in range(rows):
            if r != rk and A[r][col]:
                f = A[r][col]
                A[r] = [(x - f * y) % P for x, y in zip(A[r], A[rk])]
        rk += 1
    return rk

def local(M):
    """M = A (wire 1) ⊗ B (wire 0)?"""
    N = [[M[3 * a1 + a0][3 * b1 + b0] for a0 in range(3) for b0 in range(3)]
         for a1 in range(3) for b1 in range(3)]
    return rank(N) == 1

class Cosets:
    def __init__(self):
        self.reps = []      # (word, matrix, inverse)
    def find(self, M):
        for i, (_, R, Ri) in enumerate(self.reps):
            if local(mul(M, Ri)):
                return i
        return None
    def add(self, w):
        M = opmat(w)
        self.reps.append((w, M, inv(M)))
        return len(self.reps) - 1

if __name__ == '__main__':
    C = Cosets()
    C.add('')
    frontier = [0]
    trans = {}
    while frontier:
        nxt = []
        for i in frontier:
            w = C.reps[i][0]
            for x in 'hsHSc':
                M = opmat(w + x)
                j = C.find(M)
                if j is None:
                    j = C.add(w + x); nxt.append(j)
                trans[(i, x)] = j
        frontier = nxt
    print('cosets', len(C.reps))
    from collections import Counter
    print(Counter(w.count('c') for w, _, _ in C.reps))
    for w, _, _ in C.reps[:30]: print(repr(w))

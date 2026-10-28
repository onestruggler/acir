# Stabilizer chain normal forms for the two-qubit Clifford group (with omega).
# Levels: G0=<w>, G1=<w,S>, G2=<w,S,H>, G3=<w,S,H,s>, G4=<w,S,H,s,h>, G5=<..,Z>.
# Normal form of g in G5: r0 r1 r2 r3 r4 r5 with r_i a representative of a right coset of G_{i-1} in G_i.
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
import numpy as np
from collections import deque
from ct import MAT, mat

GENS = ['w', 'wS', 'wSH', 'wSHs', 'wSHsh', 'wSHshZ']

def key(M):
    return tuple(np.round(M.flatten() * 1e6).astype(np.int64).tolist()) if False else \
        tuple((int(round(x.real * 1e6)), int(round(x.imag * 1e6))) for x in M.flatten())

def bfs(gens):
    """All elements of <gens> with shortlex-minimal words (BFS)."""
    start = np.eye(4, dtype=complex)
    seen = {key(start): ''}
    elems = {key(start): start}
    q = deque([start])
    while q:
        M = q.popleft()
        w = seen[key(M)]
        for g in gens:
            N = M @ MAT[g]
            k = key(N)
            if k not in seen:
                seen[k] = w + g; elems[k] = N; q.append(N)
    return seen, elems

class Chain:
    def __init__(self):
        self.groups = []  # per level: dict key -> word (minimal)
        self.elems = []
        for gens in GENS:
            s, e = bfs(gens)
            self.groups.append(s); self.elems.append(e)
        # coset representatives: right cosets G_{i-1} r of G_i ; reps chosen as minimal words
        self.reps = []      # level -> list of rep words
        self.cosetOf = []   # level -> dict key(G_i element) -> coset index
        # level 0: cosets of {1} in <w>: the 8 powers
        reps0 = ['w' * k for k in range(8)]
        co0 = {}
        for k in range(8):
            co0[key(mat('w' * k))] = k
        self.reps.append(reps0); self.cosetOf.append(co0)
        for i in range(1, len(GENS)):
            sub = self.elems[i - 1]
            subkeys = list(sub.keys())
            words = sorted(self.groups[i].items(), key=lambda kv: (len(kv[1]), kv[1]))
            co = {}
            reps = []
            for k, w in words:
                if k in co: continue
                idx = len(reps); reps.append(w)
                R = self.elems[i][k]
                for sk in subkeys:
                    co[key(sub[sk] @ R)] = idx
            self.reps.append(reps); self.cosetOf.append(co)
        self.levels = len(GENS)

    def nf_parts(self, M):
        """Coset indices (c0, ..., c5) of M in the chain."""
        parts = []
        for i in reversed(range(self.levels)):
            c = self.cosetOf[i][key(M)]
            parts.append(c)
            M = M @ np.linalg.inv(mat(self.reps[i][c]))
        assert np.allclose(M, np.eye(4))
        return list(reversed(parts))

    def nf_word(self, M, top=None):
        top = self.levels - 1 if top is None else top
        parts = []
        for i in reversed(range(top + 1)):
            c = self.cosetOf[i][key(M)]
            parts.append(self.reps[i][c])
            M = M @ np.linalg.inv(mat(self.reps[i][c]))
        assert np.allclose(M, np.eye(4))
        return ''.join(reversed(parts))

if __name__ == '__main__':
    ch = Chain()
    for i in range(ch.levels):
        print(i, len(ch.groups[i]), len(ch.reps[i]), ch.reps[i])

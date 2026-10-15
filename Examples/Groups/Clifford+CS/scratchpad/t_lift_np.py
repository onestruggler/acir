# t_lift.py with numpy: meet in the middle at depth D + D.
import sys, numpy as np
exec(open('t_lift.py').read().split("D = int(sys.argv[1])")[0])
D = int(sys.argv[1]) if len(sys.argv) > 1 else 3
G = {n: np.array(M, dtype=complex) for n, M in gens.items()}
Tm = np.array(T, dtype=complex)
def k(A): return hash(np.round(A, 5).tobytes())
def grow(start, mats, D):
    seen = {k(start): []}; fr = [(start, [])]
    for _ in range(D):
        nf = []
        for (A, w) in fr:
            for n, M in mats.items():
                B = A @ M; kk = k(B)
                if kk not in seen: seen[kk] = w + [n]; nf.append((B, w + [n]))
        fr = nf
        print('  layer', len(seen), flush=True)
    return seen
left = grow(np.eye(8, dtype=complex), G, D)
Ginv = {n: M.conj().T for n, M in G.items()}
right = grow(Tm, Ginv, D)
hits = [(left[kk], list(reversed(right[kk]))) for kk in right if kk in left]
hits.sort(key=lambda h: len(h[0]) + len(h[1]))
print('hits', len(hits))
for h in hits[:5]: print(h[0] + h[1])

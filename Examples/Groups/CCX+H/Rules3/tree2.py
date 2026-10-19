"""Ball of radius 2 (and partial 3) around E in the E8-lattice graph."""
import sys, itertools, hashlib, time
from lat import G, e8_roots, orbit, THETA
from tree import word_matrix, mat_mul, S

def cols16(M):
    out = []
    for j in range(8):
        c = []
        for i in range(8):
            c.append(M[j][i][0]); c.append(M[j][i][1])
        out.append(c)
    return out

# half roots: even number of minus signs; enumerate sign vectors
HALF = [s for s in itertools.product((1, -1), repeat=8) if s.count(-1) % 2 == 0]
PAIRS = [(i, j, si, sj) for i, j in itertools.combinations(range(8), 2) for si in (1, -1) for sj in (1, -1)]

def key(M):
    C = cols16(M)
    vs = []
    for i, j, si, sj in PAIRS:
        ci, cj = C[i], C[j]
        vs.append(tuple(si * x + sj * y for x, y in zip(ci, cj)))
    for s in HALF:
        acc = [0] * 16
        for k in range(8):
            ck = C[k]
            if s[k] > 0:
                acc = [a + b for a, b in zip(acc, ck)]
            else:
                acc = [a - b for a, b in zip(acc, ck)]
        vs.append(tuple(a // 2 for a in acc))  # exact: S even
    vs.sort()
    return hashlib.sha1(repr(vs).encode()).digest()

if __name__ == "__main__":
    E = frozenset(e8_roots())
    H0E = frozenset(G["H0"](v) for v in E)
    ot = orbit(H0E, THETA)
    reps = list(ot.values())
    T = [word_matrix((w + " H0").strip()) for w in reps]
    I = word_matrix("")
    seen = {key(I): ("E",)}
    L1 = []
    for i, Ti in enumerate(T):
        k = key(Ti); assert k not in seen
        seen[k] = ("1", i); L1.append((Ti, i))
    t0 = time.time()
    cyc = 0
    L2 = []
    for Mi, i in L1:
        for j, Tj in enumerate(T):
            M2 = mat_mul(Mi, Tj)
            k = key(M2)
            if k in seen:
                if seen[k] != ("E",):
                    cyc += 1
                    if cyc <= 10:
                        print("cycle: path", i, j, "meets", seen[k], flush=True)
            else:
                seen[k] = ("2", i, j)
                if i == 0: L2.append((M2, j))
        if i % 30 == 0:
            print("level2 progress", i, len(seen), "cycles", cyc, round(time.time() - t0), flush=True)
    print("ball radius 2:", len(seen), "cycles found", cyc, flush=True)
    # level 3 from vertices at distance 2 reached through vertex L1[0]
    cyc3 = 0
    for M2, j in L2:
        for l, Tl in enumerate(T):
            M3 = mat_mul(M2, Tl)
            k = key(M3)
            if k in seen and seen[k][0] in ("E", "1", "2"):
                if seen[k] == ("1", L1[0][1]) or seen[k][:2] == ("2", 0):
                    continue  # backtrack to parent or sibling? parent only
                cyc3 += 1
                if cyc3 <= 10:
                    print("level3 meets", seen[k], "via", j, l, flush=True)
    print("level 3 (through first neighbour) hits:", cyc3, flush=True)

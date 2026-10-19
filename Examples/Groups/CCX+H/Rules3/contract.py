"""Greedy loop contraction in Gamma (test of the square complex)."""
import random, sys, time, collections
from geo import d, rel_dist, neighbours, T, I8, REPS
from tree import mat_mul

def random_loop(L, rng):
    path = [I8]
    g = I8
    while len(path) < L + 1:
        i = rng.randrange(len(T))
        h = mat_mul(g, T[i])
        if len(path) >= 2 and rel_dist(h, path[-2]) == 0:
            continue
        path.append(h); g = h
    # descend greedily
    while d(g) > 0:
        D = d(g)
        order = list(range(len(T))); rng.shuffle(order)
        for i in order:
            h = mat_mul(g, T[i])
            if d(h) == D - 1:
                break
        else:
            raise RuntimeError("no descent")
        path.append(h); g = h
    return path

def contract(path, stats):
    steps = 0
    while len(path) > 1:
        ds = [d(v) for v in path]
        D = max(ds)
        if D == 0:
            break
        i = ds.index(D)
        a, x, b = path[i - 1], path[i], path[i + 1]
        r = rel_dist(a, b)
        if r == 0:
            stats["backtrack"] += 1
            del path[i:i + 2]
            continue
        assert r == 2, r
        # common neighbours of a and b with d = D-2
        found = None
        ncommon = 0
        for _, y in neighbours(a):
            if rel_dist(y, b) == 1:
                ncommon += 1
                if found is None and d(y) == D - 2:
                    found = y
        stats[("square", ncommon)] += 1
        if found is None:
            stats["stuck"] += 1
            return False, D, ncommon
        path[i] = found
        steps += 1
    return True, 0, 0

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    for t in range(trials):
        stats = collections.Counter()
        t0 = time.time()
        p = random_loop(L, rng)
        n0 = len(p) - 1
        ok = contract(p, stats)
        print("trial", t, "loop len", n0, "ok", ok, dict(stats), round(time.time() - t0, 1), flush=True)

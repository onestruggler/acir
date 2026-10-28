"""Subcase 3.2.3: sign patterns per configuration, and the sign-free cores."""
import random, sys
from alg import *
from t32 import vkw_shape

def run(trials, seed):
    rng = random.Random(seed)
    K = ('k', 0, 1, 2, 3)
    seen = {}
    for _ in range(trials):
        n = rng.choice([6, 7, 8, 9])
        s = random_state(n, rng.randrange(3, 25), rng)
        L = level(s)
        if L[0] == 0 or L[1] == 0 or L[0] <= 4:
            continue
        u, k = wint(s)
        odd = [r for r in range(n) if u[r] % 2]
        a, b, c, d = odd[:4]
        if not (b <= 3 and c >= 4):
            continue
        r_ = gen_apply(K, s)
        ur, _ = wint(r_)
        al, be = [x for x in range(4) if ur[x] % 2]
        x, y = int(tau(ur[al])), int(tau(ur[be]))
        p, q = int(tau(u[a])), int(tau(u[b]))
        key = ((a, b), (al, be))
        seen.setdefault(key, set()).add((x, y, p, q))
    return seen

if __name__ == '__main__':
    seen = run(int(sys.argv[1]), int(sys.argv[2]))
    for k_ in sorted(seen):
        print(k_, sorted(seen[k_]))
    # sign-free cores in dimension 6, c=4, d=5
    n = 6
    for (ab, ab2) in sorted(seen):
        a, b = ab; al, be = ab2
        for par in (0, 1):
            w = [('k', al, be, 4, 5)] + ([('n', 4)] if par else []) + [('k', 0, 1, 2, 3), ('k', a, b, 4, 5)]
            M = word_apply(w, ident(n))
            print(ab, ab2, par, vkw_shape(M))

"""Case 3.2 (G = K_0123, k > 0): which subcases occur under level(G s) <= level s,
and the shape of the closing words."""
import random, sys, itertools
from alg import *

def inv_word(w):
    return list(reversed(w))

def is_signed_perm(M):
    n = len(M)
    for r in range(n):
        nz = [x for x in M[r] if x != 0]
        if len(nz) != 1 or abs(nz[0]) != 1:
            return False
    return True

def run(trials, seed):
    rng = random.Random(seed)
    stats = {}
    fails = []
    K = ('k', 0, 1, 2, 3)
    for _ in range(trials):
        n = rng.choice([6, 7, 8, 9, 10])
        s = random_state(n, rng.randrange(3, 25), rng)
        L = level(s)
        if L[0] == 0 or L[1] == 0 or L[0] <= 4:
            continue
        u, k = wint(s)
        odd = [r for r in range(n) if u[r] % 2]
        a, b, c, d = odd[:4]
        inter = len([x for x in (a, b, c, d) if x <= 3])
        r_ = gen_apply(K, s)
        Lr = level(r_)
        raises = not (Lr <= L)
        key = (inter, raises)
        stats[key] = stats.get(key, 0) + 1
        if raises:
            continue
        if inter in (1, 3):
            fails.append(('nonraising', inter, L, Lr))
            continue
        if inter == 0:
            continue
        t = nxt(s)
        if inter == 4:
            # V = syll(r) K syll(s)^-1 or (if r below) V = K syll(s)^-1 as matrices
            if Lr < L:
                m = 0
                Vm = word_apply([K] + inv_word(syll(s)), ident(n))
            else:
                m = 1
                Vm = word_apply(syll(r_) + [K] + inv_word(syll(s)), ident(n))
            if not is_signed_perm(Vm):
                fails.append(('notsp4', L, Lr))
            # levels of states along any signed perm from t: check nodd/lde of Vm-prefix...
            # (signed perms keep the level; check level(t) and the end)
            end = word_apply(npath(m, r_), r_)
            if not (level(t) < L and level(end) < L):
                fails.append(('lev4', L))
            stats[('sub4', Lr < L)] = stats.get(('sub4', Lr < L), 0) + 1
        if inter == 2:
            Mm = word_apply(syll(r_) + [K] + inv_word(syll(s)), ident(n))
            idx = [0, 1, 2, 3, c, d]
            found = vkw_shape(Mm)
            if not found:
                fails.append(('notVKW', L, Lr))
            stats[('sub2', (a, b), tuple(x for x in range(4) if wint(r_)[0][x] % 2))] = \
                stats.get(('sub2', (a, b), tuple(x for x in range(4) if wint(r_)[0][x] % 2)), 0) + 1
    return stats, fails

def vkw_shape(M):
    n = len(M)
    half_rows = []
    for r in range(n):
        nz = [(j, x) for j, x in enumerate(M[r]) if x != 0]
        if len(nz) == 1 and abs(nz[0][1]) == 1:
            continue
        if len(nz) == 4 and all(abs(x) == F(1, 2) for _, x in nz):
            half_rows.append(frozenset(j for j, _ in nz))
            continue
        return None
    if len(half_rows) == 4 and len(set(half_rows)) == 1:
        return half_rows[0]
    if len(half_rows) == 0:
        return 'sp'
    return None

def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

if __name__ == '__main__':
    stats, fails = run(int(sys.argv[1]), int(sys.argv[2]))
    for k_, v in sorted(stats.items(), key=str):
        print(k_, v)
    print(len(fails))
    for f in fails[:10]:
        print(f)

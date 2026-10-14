# Is relation (16) of the two-level presentation (rel-14: K i_k^3 =
# i_k K i_k K) within reach of the P' rules?  None of the 28 rules'
# two-level derivations (SoundLemmas) uses it.  A model of every
# two-level relation but (16): K'_[a,b] = -K_[a,b] on its block, i and
# X as usual.  If it satisfies the other eighteen relations, every rule
# of P' holds in it (their derivations go through), so item (b) for
# (16) is derivable only if it holds there too.  Checked at N = 8.
import sys
from itertools import combinations, product
import csP
import tP

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
tP.N = N
tP.LET.clear()

def I(n=N): return csP.ident(n)
mm = csP.matmul

def ig(a): return csP.two_level(N, 'i', a)
def Xg(a, b): return csP.two_level(N, 'X', a, b)

def Kmodel(sign):
    def K(a, b):
        M = [list(r) for r in csP.two_level(N, 'K', a, b)]
        for r in (a, b):
            for c in (a, b):
                M[r][c] *= sign
        return tuple(tuple(r) for r in M)
    return K

def prod(ms):
    M = I()
    for m in ms: M = mm(M, m)
    return M

def eq(A, B): return csP.key(A) == csP.key(B)

def check_relations(K, skip16=True):
    bad = {}
    idx = range(N)
    def note(name, ok):
        if not ok: bad[name] = bad.get(name, 0) + 1
    for j in idx:
        note('order-i', eq(prod([ig(j)] * 4), I()))
    for j, k in combinations(idx, 2):
        note('order-X', eq(prod([Xg(j, k)] * 2), I()))
        note('order-K', eq(prod([K(j, k)] * 8), I()))
        note('rel-13', eq(prod([K(j, k), ig(k), ig(k)]), prod([Xg(j, k), K(j, k)])))
        note('rel-14', eq(prod([K(j, k)] + [ig(k)] * 3),
                         prod([ig(k), K(j, k), ig(k), K(j, k)])))
        note('rel-15', eq(prod([K(j, k), ig(j), ig(k)]), prod([ig(j), ig(k), K(j, k)])))
        note('rel-16', eq(prod([K(j, k), K(j, k), ig(j), ig(k)]), I()))
        for l in idx:
            if l in (j, k): continue
            note('comm-iK', eq(mm(ig(l), K(j, k)), mm(K(j, k), ig(l))))
            if l > k:
                note('swap-KX', eq(mm(K(k, l), Xg(j, k)), mm(Xg(j, k), K(j, l))))
                note('swap-KX2', eq(mm(K(j, l), Xg(k, l)), mm(Xg(k, l), K(j, k))))
    prs = list(combinations(idx, 2))
    for (j, k), (l, m) in product(prs, prs):
        if len({j, k, l, m}) == 4:
            note('comm-XK', eq(mm(Xg(j, k), K(l, m)), mm(K(l, m), Xg(j, k))))
            note('comm-KK', eq(mm(K(j, k), K(l, m)), mm(K(l, m), K(j, k))))
            if j < l and k < m:
                note('rel-17', eq(prod([K(j, k), K(l, m), K(j, l), K(k, m)]),
                                  prod([K(j, l), K(k, m), K(j, k), K(l, m)])))
    return bad

# The letters of P' read through asG, with K replaced.
def letter_model(K):
    def L(name):
        kind = name[0]
        if kind == 'iib':
            _, a, b = name
            return prod([ig(a), ig(b), ig(b), ig(b)])
        if kind == 'mX':
            _, c, a, b = name
            return prod([ig(c), ig(c), Xg(a, b)])
        if kind == 'XX':
            _, a, b, c, d = name
            return mm(Xg(a, b), Xg(c, d))
        _, a, b, c, d = name
        return prod([K(a, b), K(c, d), ig(c), ig(d)])
    return L

def word_model(L, w):
    return prod([L(x) for x in w])

def traverse(c, gens):
    out = []
    for g in gens:
        out += tP.act_word(c, g)
        c = (c + tP.deg(g)) % 4
    return out, c

if __name__ == '__main__':
    Km = Kmodel(-1)
    print('true K, relations failing:', check_relations(Kmodel(1)))
    print('K\' = -K, relations failing:', check_relations(Km))
    L = letter_model(Km)
    # item (b) for rel-14 at every coset and every pair
    fails = 0; tot = 0
    for j, k in combinations(range(N), 2):
        lhs = [('K', j, k)] + [('i', k)] * 3
        rhs = [('i', k), ('K', j, k), ('i', k), ('K', j, k)]
        for c in range(4):
            wl, cl = traverse(c, lhs)
            wr, cr = traverse(c, rhs)
            tot += 1
            if cl != cr or not eq(word_model(L, wl), word_model(L, wr)):
                fails += 1
                if fails <= 3: print('rel-14 obligation fails in the model:', c, (j, k))
    print(f'rel-14 item (b) obligations failing in the model: {fails}/{tot}')

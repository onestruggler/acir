# The K-free fragment rules for the Clifford+CS >= 4-wire design: the
# phase analogue of Real-Clifford+CH's Figure8Free (20)-(34), every
# instance checked on exact matrices at N (the tB.py analogue).
# Letters: pp a b = i_a i_b^-1, px s a b = i_s^2 X_ab, dx = X X.
import sys
import csP
from itertools import combinations, permutations, product

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5

def pp(a, b):
    return csP.matmul(csP.two_level(N, 'i', a), csP.minv('i', N, b))
def px(s, a, b):
    m = csP.matmul(csP.two_level(N, 'i', s), csP.two_level(N, 'i', s))
    a, b = min(a, b), max(a, b)
    return csP.matmul(m, csP.two_level(N, 'X', a, b))
def dx(a, b, c, d):
    return csP.matmul(csP.two_level(N, 'X', min(a,b), max(a,b)),
                      csP.two_level(N, 'X', min(c,d), max(c,d)))

E = csP.ident(N)
def mp(*Ms):
    R = E
    for M in Ms: R = csP.matmul(R, M)
    return R
def eq(A, B): return csP.key(A) == csP.key(B)

fails = []
def check(tag, A, B):
    if not eq(A, B): fails.append(tag)

idx = range(N)
cnt = 0
# (20') pp a a = eps ; (20'') pp^4 = eps
for a in idx:
    check(('20a', a), pp(a, a), E); cnt += 1
for a, b in permutations(idx, 2):
    P = pp(a, b)
    check(('20b', a, b), mp(P, P, P, P), E); cnt += 1
    # (21') pp a b . pp b a = eps
    check(('21a', a, b), mp(P, pp(b, a)), E); cnt += 1
# (21'') pp's commute (sample all pairs of pairs)
for a, b in permutations(idx, 2):
    for c, d in permutations(idx, 2):
        check(('21b', a, b, c, d), mp(pp(a, b), pp(c, d)), mp(pp(c, d), pp(a, b))); cnt += 1
# (22') pp a b . pp b c = pp a c
for a in idx:
    for b in idx:
        for c in idx:
            check(('22', a, b, c), mp(pp(a, b), pp(b, c)), pp(a, c)); cnt += 1
# (23') pp a a' ^2 = px a a a' ^2   (a' = a+1)
for a in range(N - 1):
    check(('23', a), mp(pp(a, a + 1), pp(a, a + 1)), mp(px(a, a, a + 1), px(a, a, a + 1))); cnt += 1
# (24) braid on consecutive triples
for a in range(N - 2):
    l = mp(px(a, a, a + 1), px(a + 1, a + 1, a + 2), px(a, a, a + 1))
    r = mp(px(a + 1, a + 1, a + 2), px(a, a, a + 1), px(a + 1, a + 1, a + 2))
    check(('24', a), l, r); cnt += 1
# (25)-(28): shrinking a letter by parity of the gap
par = lambda k: k % 2 == 1
for a in idx:
    for c in idx:
        if a + 1 < c:
            ap = a + 1
            if par(c - a):
                check(('25', a, c), px(a, a, c), mp(px(ap, a, ap), px(ap, ap, c), px(a, a, ap))); cnt += 1
                check(('26', a, c), px(c, a, c), mp(px(ap, a, ap), px(c, ap, c), px(a, a, ap))); cnt += 1
            else:
                cp = c - 1
                check(('27', a, c), px(a, a, c), mp(px(cp, cp, c), px(a, a, cp), px(c, cp, c))); cnt += 1
                check(('28', a, c), px(c, a, c), mp(px(cp, cp, c), px(cp, a, cp), px(c, cp, c))); cnt += 1
# (29) px a a a' . px a' a a' = eps
for a in range(N - 1):
    check(('29', a), mp(px(a, a, a + 1), px(a + 1, a, a + 1)), E); cnt += 1
# (30') px c a b = pp c a ^2 . px a a b
for c in idx:
    for a, b in permutations(idx, 2):
        if c != a and c != b:
            check(('30', c, a, b), px(c, a, b), mp(pp(c, a), pp(c, a), px(a, a, b))); cnt += 1
# (31') the exchange renames a phase pair: px a a a' . pp x y = pp sx sy . px a a a'
for a in range(N - 1):
    ap = a + 1
    sig = lambda t: ap if t == a else (a if t == ap else t)
    for x in idx:
        for y in idx:
            check(('31', a, x, y), mp(px(a, a, ap), pp(x, y)), mp(pp(sig(x), sig(y)), px(a, a, ap))); cnt += 1
# (32) disjoint consecutive letters commute
for a in range(N - 1):
    for b in range(a + 2, N - 1):
        l = mp(px(a, a, a + 1), px(b, b, b + 1))
        check(('32', a, b), l, mp(px(b, b, b + 1), px(a, a, a + 1))); cnt += 1
# (33) px b a b = px b b a (the letter only cares about its index set)
for b, a in permutations(idx, 2):
    check(('33', b, a), px(b, a, b), px(b, b, a)); cnt += 1
# (34') dx a b c d = px a a b . px b c d
for a, b in permutations(idx, 2):
    for c, d in permutations(idx, 2):
        if len({a, b, c, d}) == 4:
            check(('34', a, b, c, d), dx(a, b, c, d), mp(px(a, a, b), px(b, c, d))); cnt += 1

print(f'N={N}: {cnt - len(fails)}/{cnt} fragment-rule instances sound')
for f in fails[:10]: print('FAIL', f)

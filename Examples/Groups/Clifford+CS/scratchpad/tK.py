# The KKb-letter local algebra: raw-index candidates for the (35)-(46)
# analogues, each spelling checked on exact matrices at N.
import sys
import csP
from itertools import combinations, permutations

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8

def pp(a, b):
    return csP.matmul(csP.two_level(N, 'i', a), csP.minv('i', N, b))
def px(s, a, b):
    m = csP.matmul(csP.two_level(N, 'i', s), csP.two_level(N, 'i', s))
    a, b = min(a, b), max(a, b)
    return csP.matmul(m, csP.two_level(N, 'X', a, b))
def kk(a, b, c, d):
    return csP.matmul(csP.two_level(N, 'K', min(a,b), max(a,b)),
                      csP.minv('K', N, min(c,d), max(c,d)))
def dx(a, b, c, d):
    return csP.matmul(csP.two_level(N, 'X', min(a,b), max(a,b)),
                      csP.two_level(N, 'X', min(c,d), max(c,d)))
E = csP.ident(N)
def mp(*Ms):
    R = E
    for M in Ms: R = csP.matmul(R, M)
    return R
def eq(A, B): return csP.key(A) == csP.key(B)

report = []
def check(tag, A, B):
    report.append((tag, eq(A, B)))

a, b, c, d = 0, 1, 2, 3
e, f, g, h = 4, 5, 6, 7

# K1: inverses.  KKb[ab,cd] . KKb[cd,ab] = eps
check('K1  kk(ab,cd) kk(cd,ab) = e', mp(kk(a,b,c,d), kk(c,d,a,b)), E)
# K2: the square is a phase word (the (41)-analogue):
#     kk^2 = K_ab^2 K_cd^-2 = (i_a i_b)^-1 (i_c i_d) = pp c a . pp d b
check('K2  kk^2 = pp(c,a) pp(d,b)', mp(kk(a,b,c,d), kk(a,b,c,d)), mp(pp(c,a), pp(d,b)))
# K3: bridging (the (42)-analogue): kk[ab,cd] = kk[ab,ef] . kk[ef,cd]
check('K3  kk(ab,cd) = kk(ab,ef) kk(ef,cd)', kk(a,b,c,d), mp(kk(a,b,e,f), kk(e,f,c,d)))
# K4: disjoint letters commute (sample)
check('K4  kk(ab,cd) px(e,e,f) comm', mp(kk(a,b,c,d), px(e,e,f)), mp(px(e,e,f), kk(a,b,c,d)))
check('K4b kk(ab,cd) pp(e,f) comm', mp(kk(a,b,c,d), pp(e,f)), mp(pp(e,f), kk(a,b,c,d)))
# K5: the -1-1 pair on a K-pair's own indices passes (the (39)-analogue)
check('K5  pp(a,b)^2 kk = kk pp(a,b)^2', mp(pp(a,b), pp(a,b), kk(a,b,c,d)),
      mp(kk(a,b,c,d), pp(a,b), pp(a,b)))
# K6: rel-15 lifted: i_a i_b passes K_ab, so pp a x . pp b x -shapes:
#     (i_a i_b) kk = kk (i_a i_b):  i_a i_b = pp(a,x) pp(b,y) ... use
#     pp(a,e) pp(b,e): i_a i_b i_e^-2; i_e^-2 passes; so test
check('K6  pp(a,e) pp(b,e) kk = kk pp(a,e) pp(b,e)',
      mp(pp(a,e), pp(b,e), kk(a,b,c,d)), mp(kk(a,b,c,d), pp(a,e), pp(b,e)))
# K7: rel-13 lifted: K_ab (-1_b) = X_ab K_ab; with letters the -1 is a
#     pp-square whose second -1 sits on a fresh index, where it becomes
#     the sign of the px: kk . (pp b e)^2 = px(e;a,b) . kk
check('K7  kk (pp b,e)^2 = px(e,a,b) kk', mp(kk(a,b,c,d), pp(b,e), pp(b,e)),
      mp(px(e,a,b), kk(a,b,c,d)))
# K7b: the sign on the first index costs a -1-1 on the pair (which
#      passes kk, K5): kk . (pp a e)^2 = px(e;a,b) . (pp a b)^2 . kk
check('K7b kk (pp a,e)^2 = px(e,a,b) (pp a b)^2 kk',
      mp(kk(a,b,c,d), pp(a,e), pp(a,e)),
      mp(px(e,a,b), pp(a,b), pp(a,b), kk(a,b,c,d)))
# K8: the exchange of the pair conjugates kk to (pp a b)^2 . kk
#     (px(b;a,b)^-1 = px(a;a,b)):
check('K8  px(b,a,b) kk px(a,a,b) = (pp a b)^2 kk',
      mp(px(b,a,b), kk(a,b,c,d), px(a,a,b)),
      mp(pp(a,b), pp(a,b), kk(a,b,c,d)))
# K9: XX renames a K-pair (swap rules): dx[ae,bf] kk[ab,..] dx = kk[ef,..]
check('K9  dx(a,e,b,f) kk(a,b,c,d) dx(a,e,b,f) = kk(e,f,c,d)',
      mp(dx(a,e,b,f), kk(a,b,c,d), dx(a,e,b,f)), kk(e,f,c,d))
# K10: rel-17 lifted (the K-Yang-Baxter): with all dets paired off:
#      kk[ab,ef] kk[cd,gh] kk[ac,ef] kk[bd,gh] = kk[ac,ef] kk[bd,gh] kk[ab,ef] kk[cd,gh]
check('K10 rel-17 bridged through ef,gh',
      mp(kk(a,b,e,f), kk(c,d,g,h), kk(a,c,e,f), kk(b,d,g,h)),
      mp(kk(a,c,e,f), kk(b,d,g,h), kk(a,b,e,f), kk(c,d,g,h)))
# K11: rel-14 in letter form (the found act word):
#      pp(b,a) [pp(e,a), kk(ab,cd)] = K_ab i_a^-1 ... as a letter rule:
#      kk[ab,cd] . V = V' . kk[ab,cd] shapes are complex; check the raw
#      identity underlying the act table instead:
#      pp(b,a) pp(e,a) kk(a,b,c,d) pp(a,e) kk(c,d,a,b) = K_ab i_a^-1
target = mp(csP.two_level(N, 'K', a, b), csP.minv('i', N, a))
check('K11 the act-table K-word', mp(pp(b,a), pp(e,a), kk(a,b,c,d), pp(a,e), kk(c,d,a,b)), target)

w = max(len(t) for t, _ in report)
okc = 0
for t, ok in report:
    print(f'{t:<{w}}  {"OK" if ok else "FAIL"}')
    okc += ok
print(f'{okc}/{len(report)}')

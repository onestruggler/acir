"""Check (6a), Proposition A.16 and the lines of its printed proof (0-based a..h = 0..7)."""
from alg import *
a, b, c, d, e, f, g, h = range(8)
N = lambda x: ('n', x)
X = lambda x, y: ('x', x, y)
K = lambda *xs: ('k',) + xs

def mat(w):
    return word_apply(list(w), ident(8))

C = [K(e, f, g, h), K(a, b, c, d), X(d, e), K(a, b, c, d), K(e, f, g, h)]
r6a_l = [N(a), N(e), X(a, e)] + C + [X(a, e), N(a), N(e)]
print('(6a):', mat(r6a_l) == mat(C))
a16_r = [N(a), N(h), X(a, h)] + C + [X(a, h), N(a), N(h)]
print('A.16 as stated:', mat(a16_r) == mat(C))
C2 = [K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h)]
print('C2 = K_efgh K_abcd K_abce K_dfgh equal to C?', mat(C2) == mat(C))
lines = [
 C2 + [X(a, h), N(a), N(h)],
 [X(e, h), X(e, h)] + C2 + [X(a, h), N(a), N(h)],
 [X(e, h), K(e, f, g, h), X(f, h), X(g, h), X(f, h), N(f), N(g), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(a, h), N(a), N(h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), X(f, h), X(g, h), X(f, h), N(f), N(g), K(d, f, g, h), X(a, h), N(a), N(h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), X(f, g), N(f), N(g), K(d, f, g, h), X(a, h), N(a), N(h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(d, h), X(a, h), N(a), N(h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), N(a), N(d), X(d, h), X(a, h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(a, d), X(a, d), N(a), N(d), X(d, h), X(a, h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(a, d), N(a), N(d), X(a, d), X(d, h), X(a, h)],
 [X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(a, d), N(a), N(d), X(d, h)],
 [X(e, h), X(a, e), N(a), N(e), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(d, h)],
 [X(e, h), X(a, e), N(a), N(e), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), N(f), N(g), X(f, g), K(d, f, g, h)],
 [X(e, h), X(a, e), N(a), N(e), K(e, f, g, h), N(f), N(g), X(f, g), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h)],
 [X(e, h), X(a, e), N(a), N(e), X(e, h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h)],
 [X(e, h), X(a, e), X(e, h), N(a), N(h), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h)],
 [X(a, h), N(a), N(h)] + C2,
]
for i in range(1, len(lines)):
    print('line', i, mat(lines[i]) == mat(lines[i - 1]))
# which relation does the step line9->line10 use: X_ad N_a N_d K... = X_ae N_a N_e K...
w1 = [K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h), X(a, d), N(a), N(d)]
w2 = [X(a, e), N(a), N(e), K(e, f, g, h), K(a, b, c, d), K(a, b, c, e), K(d, f, g, h)]
print('core step (C2 X_ad N_a N_d = X_ae N_a N_e C2):', mat(w1) == mat(w2))

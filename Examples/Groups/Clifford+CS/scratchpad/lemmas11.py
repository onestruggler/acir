# The first same-pair relation from the rule ck-tct (X_a CK(a,t) X_a passes
# Toff(t;b,c) CS(a,t) Toff(t;b,c)):
#   Q1:  PP . b = b^-1 . PP,   b = K0^-1 PP K0   (L(iZ) L(iX) L(iZ)^-1 = L(iX)^-1)
# Route: PP = g . PPw3^-1 by the merge (g = CS12 CCZ012, PPw3 = X3 PP X3);
# PPw3 passes b (the rule, under K0: the white-on-3 letters of K0 PPw3 K0^-1
# pass PP); g b g^-1 = b^-1 (CS12 passes b; CCZ012 = Lambda_12(Z) turns b
# over, under K0 the Toffoli turning PP over).
from deriv import Derivation, show, fp, cczs, norm, inv
import passes as P
from passes import L
import gadgets4
from lemmas5 import T, C3, C3d, PP3

PP = list(PP3)
K0, Kd0, X3 = ('K', 0), ('Kd', 0), ('X', 3)
CK30, CKd30 = ('CK', 3, 0), ('CKd', 3, 0)
CS12, D = ('CS', 1, 2), cczs(0, 1, 2)
g = [CS12, D]
b = [Kd0] + PP + [K0]
PPw3 = [X3] + PP + [X3]
PPu = P.units(PP)

# ---- the rule at the gadget: X3 CK30 X3 passes PP
NK = (X3, CK30, X3)
d = Derivation(P.pname([NK], PPu), list(NK) + PP, PP + list(NK), L)
d.ckt(0)                                   # T C T  X3 CK30 X3  Cd
d.win(3, 7, [C3d, X3, CK30, X3])
d.done()
NKi = (X3, CKd30, X3)
P.inverse_pass([NKi], PPu)
print('rule passes PP')

# ---- U = X3 (K0 CS03 K0^-1) X3 and its inverse pass PP, through the rule
def lam_pass(cs):
    """X3 K0 cs Kd0 X3 passes PP, cs = CS03 or its inverse."""
    U = (X3, K0, cs, Kd0, X3)
    xc = norm([X3, cs, X3]) if False else None
    mid = P.simplify([X3, cs, X3])              # S0 CSd03 or Sd0 CS03
    form = [NK] + [(h,) for h in mid] + [NKi]
    for u in form[1:-1]: P.prove([u], PPu)
    name = P.pname([U], PPu)
    d = Derivation(name, list(U) + PP, PP + list(U), L)
    d.win(0, 5, P.flat(form))
    pos = len(P.flat(form))
    for u in reversed(form):
        pos -= len(P.flatu(u)); P.apply_pass(d, pos, [u], PPu)
    n = len(PP)
    d.win(n, len(d.cur), list(U))
    d.done(); return U

U1, U2 = lam_pass(C3), lam_pass(C3d)

# ---- H = K0 PPw3 K0^-1 in the unit form [CCZ012, U1, CCZ012, U2], which passes PP
Hu = [(D,), U1, (D,), U2]
Hw = P.flat(Hu)
d = Derivation('K0-PPw3-Kd0', [K0] + PPw3 + [Kd0], Hw, L)
d.comm(0)                                           # X3 K0 T C T Cd X3 Kd0
# K0 T C T Cd Kd0 -> (K0 T Kd0)(K0 C Kd0)(K0 T Kd0)(K0 Cd Kd0)
for k in (5, 4, 3): d.win(k, k, [Kd0, K0])
d.comm(12)                                          # Kd0 before the last X3
d.win(1, 4, [D]); d.win(5, 8, [D])                  # X3 D (K0 C Kd0) D (K0 Cd Kd0) X3
d.comm(0)                                           # D X3 ...
d.win(5, 5, [X3, X3]); d.comm(6)
assert d.cur == Hw, show(d.cur)
d.done()
P.prove(Hu, PPu)
print('H passes PP')

# ---- PPw3 passes b
name = P.pname([P.Col([3], PPu)], P.units(b))
d = Derivation(name, PPw3 + b, b + PPw3, L)
d.win(0, 0, [Kd0, K0])                              # Kd0 K0 PPw3 Kd0 PP K0
d.lemma('K0-PPw3-Kd0', 1)                           # Kd0 Hw PP K0
P.apply_pass(d, 1, Hu, PPu)                         # Kd0 PP Hw K0
d.lemma('K0-PPw3-Kd0', 1 + len(PP), forward=False)  # Kd0 PP K0 PPw3 Kd0 K0
d.win(len(d.cur) - 2, len(d.cur), [])
d.done()
print('PPw3 passes b')

# ---- g b = b^-1 g
bi = inv(b)
d = Derivation('D-b', [D] + b, bi + [D], L)
d.win(0, 2, [Kd0, T])                               # Kd0 T T C T Cd K0
d.win(1, 3, [])                                     # Kd0 C T Cd K0
d.win(4, 4, [T, T])                                 # Kd0 C T Cd T T K0
d.win(5, 7, [K0, D])
d.done()
cs12b = P.prove([(CS12,)], P.units(b))
cs12bi = P.prove([(CS12,)], P.units(bi))
d = Derivation('g-b', g + b, bi + g, L)
d.lemma('D-b', 1)                                   # CS12 bi D
d.lemma(cs12bi, 0)                                  # bi CS12 D
d.done()

# ---- PP = g . PPw3^-1, and Q1
PPw3i = inv(PPw3)
d = Derivation('PP-g', PP, g + PPw3i, L)
P.insert_inverse(d, len(PP), PPw3)                  # PP PPw3 PPw3^-1
d.lemma('merge3', 0)
d.done()
w3b = P.pname([P.Col([3], PPu)], P.units(b))
inv_pass = P.inverse_pass([tuple(PPw3i)], P.units(b))
d = Derivation('Q1', PP + b, bi + PP, L)
d.lemma('PP-g', 0)                                  # g PPw3^-1 b
d.lemma(inv_pass, len(g))                           # g b PPw3^-1
d.lemma('g-b', 0)                                   # b^-1 g PPw3^-1
d.lemma('PP-g', len(bi), forward=False)             # b^-1 PP
d.done()
print('Q1 derived: PP . b = b^-1 . PP')

# The merge of a black and a white control of the phase gadget, and with
# it the commutation of adjacent gadgets (targets 0 and 1, all black,
# sharing the basis state 1111).
#   merge3:  PP . X3 PP X3 = L_12(iZ_0) = CS12 CCZ012
#   adj01:   PP_0 PP_1 = PP_1 PP_0
# PP_1 = Q1 . X3 PP_1^-1 X3 by the merge at target 1, Q1 = CS02 CCZ012
# passes PP_0 (named diagonals), and X3 PP_1^-1 X3 passes PP_0
# (separated on wire 3).
from deriv import Derivation, show, fp, cczs, norm, inv, relabel
import passes as P
from passes import L
from gadgets4 import setup, canon
from lemmas5 import T, C3, C3d, PP3

G = setup()
X3 = ('X', 3); S0, Sd0 = ('S', 0), ('Sd', 0)
CS12, D = ('CS', 1, 2), cczs(0, 1, 2)
Qm = [CS12, D]

def cancel_inverse(d, k, w):
    """at k: w then inv(w): cancel from the middle by windows."""
    n = len(w)
    for j in range(n):
        m = k + n - 1 - j
        d.win(m, m + 2, [])

# ---- merge3
d = Derivation('merge3', PP3 + [X3] + PP3 + [X3], Qm, L)
# X3 T C T Cd X3 -> T (S0 Cd) T (C Sd0): X3 through the second PP letter by letter
p = 4
d.comm(p)                                          # T X3 ...
d.win(p + 1, p + 3, [S0, C3d, X3])                 # T S0 Cd X3 T Cd X3
d.comm(p + 3)                                      # T S0 Cd T X3 Cd X3
d.win(p + 4, p + 7, [C3, Sd0])                     # T C T Cd | T S0 Cd T C Sd0
# T S0 Cd T = (T S0 T)(T Cd T): insert T T after S0
d.win(p + 2, p + 2, [T, T])                        # ... T S0 T T Cd T C Sd0
d.win(p, p + 3, [S0] + Qm)                         # T C T Cd | S0 CS12 CCZ012 T Cd T C Sd0
# (T C T) passes Cd, S0, CS12, CCZ012 then cancels with T Cd T
TCT = [T, C3, T]
TCTu = [(T,), (C3,), (T,)]
P.register('C3d-A', [(C3d,)], TCTu)
for g in [C3d, S0, CS12, D]:
    nm = P.prove([(g,)], TCTu)
    i = d.cur.index(g, 3)
    assert d.cur[i - 3:i] == TCT, show(d.cur)
    d.lemma(nm, i - 3, forward=False)
i = 4
assert d.cur[i:i + 6] == TCT + [T, C3d, T], show(d.cur)
d.win(i + 2, i + 4, []); d.win(i + 1, i + 3, []); d.win(i, i + 2, [])
# Cd S0 CS12 CCZ012 C Sd0 -> CS12 CCZ012 (named diagonals)
e = P.diag_canon(d, 0, len(d.cur))
assert d.cur == P.canon_letters(Qm), show(d.cur)
if d.cur != Qm: d.win(0, len(d.cur), Qm)
L = d.done()

# ---- the adjacent commutation PP_0 PP_1 = PP_1 PP_0
PP0, PP1 = canon(0), canon(1)
m1 = relabel('merge3', (1, 0, 2, 3), L)            # PP1 . X3 PP1 X3 = CS02 CCZ012
Q1 = L[m1][1]
PP1i = inv(PP1)
def insert_inverse(d, k, w):
    """at k insert w inv(w), pair by pair from the outside in."""
    iw = inv(w)
    for j, g in enumerate(w):
        d.win(k + j, k + j, [g, iw[len(w) - 1 - j]])

# PP1 = Q1 . X3 PP1^-1 X3
d = Derivation('PP1-split', PP1, Q1 + [X3] + PP1i + [X3], L)
n = len(PP1)
d.win(n, n, [X3, X3])
insert_inverse(d, n + 1, PP1)                       # PP1 X3 PP1 PP1^-1 X3
d.win(2 * n + 1, 2 * n + 1, [X3, X3])               # PP1 X3 PP1 X3 X3 PP1^-1 X3
d.lemma(m1, 0)
L = d.done()

# PP_0 passes X3 PP1^-1 X3 (separated on wire 3): from PP_0 passes X3 PP1 X3
sep = P.prove(P.units(PP0), [P.Col([3], P.units(PP1))])
d = Derivation('PP0-sep-inv', PP0 + [X3] + PP1i + [X3], [X3] + PP1i + [X3] + PP0, L)
# insert (X3 PP1 X3)(X3 PP1 X3)^-1 in front, pass PP0 across X3 PP1 X3 backwards, cancel
W1 = [X3] + PP1 + [X3]; W1i = inv(W1)
insert_inverse(d, 0, W1i)                           # W1i W1 PP0 W1i
k = len(W1i)
d.lemma(sep, k, forward=False)                      # W1i PP0 W1 W1i  (W1 PP0 -> PP0 W1 backwards)
cancel_k = k + len(PP0)
for j in range(len(W1)):
    m = cancel_k + len(W1) - 1 - j
    d.win(m, m + 2, [])
L = d.done()

# PP_0 PP_1 = PP_1 PP_0
Q1u = P.units(Q1)
qpass = P.prove(Q1u, P.units(PP0))
d = Derivation('adj01', PP0 + PP1, PP1 + PP0, L)
n0 = len(PP0)
d.lemma('PP1-split', n0)                             # PP0 Q1 X3 PP1i X3
d.lemma(qpass, 0, forward=False)                     # Q1 PP0 X3 PP1i X3
d.lemma('PP0-sep-inv', len(Q1))                      # Q1 X3 PP1i X3 PP0
d.lemma('PP1-split', 0, forward=False)               # PP1 PP0
L = d.done()
print('adjacent commutation derived')

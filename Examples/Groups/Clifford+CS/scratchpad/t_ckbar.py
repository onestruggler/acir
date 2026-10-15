# The candidate fourth four-wire rule, ck-tct with Barenco's L_23(V^2) in
# place of the Toffoli: is it sound, and which middles/units does the
# hybrid gadget need?  Exact over Q(i) with fractions, wires 0..3 (wire 0
# the bottom), letters as in deriv.py.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show, inv
from dec import barenco, G_ki

def bar(t, b, c): return norm(barenco('SSKS', b, c, t))
def nc(a, t, g): return [('X', a), (g, a, t), ('X', a)]

def commutes(A, B): return fp(A + B) == fp(B + A)

t, a, b, c = 1, 0, 2, 3
B = bar(t, b, c)
for mid in ('CS', 'CK'):
    P = B + [(mid, a, t)] + inv(B)
    for u in ('CS', 'CK'):
        print(f'unit X{a} {u}({a}->{t}) X{a} vs Bar {mid}({a},{t}) Bar^-1:', commutes(nc(a, t, u), P))
# the rule as ck-tct states it, for comparison
T = [('TOFF', t, b, c)]
print('ck-tct:', commutes(nc(a, t, 'CK'), T + [('CS', a, t)] + T))
# the hybrid core passes white units on its target and its controls
KI = norm(G_ki(4))
for cc in (1, 2, 3):
    for x in (0,) + tuple(w for w in (1, 2, 3) if w != cc):
        for g in ('CS', 'CK'):
            U = nc(cc, x, g)
            print(f'  X{cc} {g}({cc}->{x}) X{cc} passes KI:', commutes(U, KI))

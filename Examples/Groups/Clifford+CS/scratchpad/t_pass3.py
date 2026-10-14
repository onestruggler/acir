import passes as P
from deriv import show
import gadgets4
G = gadgets4.setup()
PPu = G[0]
K0, Kd0 = ('K', 0), ('Kd', 0)
b = [(Kd0,)] + PPu + [(K0,)]          # K^-1 PP K = L(iX)
for nm, A, B in [('PP vs white-3 L(iX)', PPu, [P.Col([3], b)]),
                 ('L(iX) vs white-3 PP', b, [P.Col([3], PPu)]),
                 ('L(iX) vs white-3 L(iX)', b, [P.Col([3], b)])]:
    try: P.prove(A, B); print('PROVED', nm)
    except P.Fail as e: print('FAIL', nm, str(e)[:400])

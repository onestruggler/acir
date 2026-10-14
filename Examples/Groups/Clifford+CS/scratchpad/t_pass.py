import passes as P
from deriv import Derivation, show
from lemmas5 import T, T13, C3, C3d, C2, C2d, PP3, PP2
from lemmas8 import L
PPu = P.units(PP3); PP2u = P.units(PP2)
P.add_form(PPu, PP2u, 'S2')
for test in ([(C2,)], [(C2d,)], [(('S', 0),)], [(('CS', 1, 2),)]):
    try: print('OK', P.prove(test, PPu)[:60])
    except P.Fail as e: print('FAIL', str(e)[:300])
for S in ([3], [2, 3], [1, 2, 3]):
    A = [P.Col(S, PPu)]
    try:
        n = P.prove(A, PPu); print('PROVED', S)
    except P.Fail as e:
        print('FAIL', S, str(e)[:400])

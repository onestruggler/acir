"""Spin-lift signs of a few relations at a given width (n <= 5)."""
import sys
from spin import lift_sign

def show(name, n, word):
    r = lift_sign(n, word)
    s = '+1' if r.real > 0.5 else '-1' if r.real < -0.5 else repr(r)
    print(f'n={n}  {name:28s} {s}')

for n in (4, 5):
    for g in [('X', 0), ('CX', 1, 0), ('CCX', 2, 1, 0), ('HH', 0, 1), ('H', 0)]:
        show(f'{g} squared', n, [g, g])
n = 5
A, B = ('CCX', 3, 4, 1), ('CCX', 1, 2, 0)   # Barenco C^3X = ABAB, borrowed wire 1
show('(AB)^4 = (C3X)^2', n, [A, B] * 4)
show('[C3X, X1] (borrowed wire)', n, [A, B, A, B, ('X', 1)] * 2)
show('[CCX(234), CX(01)]', n, [('CCX', 3, 4, 2), ('CX', 1, 0)] * 2)
show('[CX(34), CCX(012)]', n, [('CX', 4, 3), ('CCX', 1, 2, 0)] * 2)
show('[X0, CCX(234)]', n, [('X', 0), ('CCX', 3, 4, 2)] * 2)
show('[HH01, CCX(234)]', n, [('HH', 0, 1), ('CCX', 3, 4, 2)] * 2)

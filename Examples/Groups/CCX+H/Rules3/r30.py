from lat import G, apply
from fractions import Fraction as F
def mat(word):
    cols = []
    for j in range(8):
        v = tuple((F(1 if i == j else 0), F(0)) for i in range(8))
        cols.append(apply(" ".join(reversed(word.split())), v) if word else v)
    return cols
lhs = mat("CCX0 H0 CCX0 H0 CCX0 H0 CCX0 H0")
rhs = mat("H1 CX12 H1")
print("(CCX H)^4 == CZ on wires 1,2:", lhs == rhs)
print("CCX CCZ CCX == X0 CCZ X0:", mat("CCX0 H0 CCX0 H0 CCX0") == mat("X0 H0 CCX0 H0 X0"))

"""The 18 rules of Figure 1, in time order, wire 0 at the bottom."""
from qt import *

T, B = 1, 0          # top and bottom of two wires
T3, M3, B3 = 2, 1, 0  # three wires

RULES = {
    'C1': (0, nu(6), []),
    'C2': (1, H() * 4, []),
    'C3': (1, S() * 3, []),
    'C4': (1, S() * 2 + H() + S() * 2 + H() + S() * 2 + H(), nu()),
    'C5': (1, S() + Sp(), Sp() + S()),
    'C6': (2, CZ() * 3, []),
    'C7': (2, SWAP() + SWAP(), []),
    'C8': (2, S(T) + CZ(), CZ() + S(T)),
    'C9': (2, H(T) * 2 + CZ() + CZ(), CZ() + H(T) * 2),
    'C10': (2, S(T) + SWAP(), SWAP() + S(B)),
    'C11': (2, H(T) + SWAP(), SWAP() + H(B)),
    'C12': (2, CZ() + SWAP(), SWAP() + CZ()),
    'C13': (2, S(T) + XC(), XC() + CZ() + S(T) + Sp(B) + omega() * 2),
    'C14': (2, CZ() + XC(), XC() + CZ() + Sp(B) + S(B) + omega()),
    'C15': (3, CZ(0) + CZ(1), CZ(1) + CZ(0)),
    'C16': (3, SWAP(1) + SWAP(0) + SWAP(1), SWAP(0) + SWAP(1) + SWAP(0)),
    'C17': (3, CZ(0) + SWAP(1) + SWAP(0), SWAP(1) + SWAP(0) + CZ(1)),
    'C18': (3, CX(1) + CZ(0), CZ(0) + CX(1) + CZ02()),
}

if __name__ == '__main__':
    gate_diag_ok()
    for name, (n, l, r) in RULES.items():
        print(name, eq(l, r, n))

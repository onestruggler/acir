"""The cores of Clement's diagrams (20) and (30) on local labels 0..5
(0, 1: the hard pair; 2, 3: their partners; 4, 5: the extras), as words
in operator order (rightmost first)."""


def H(i, j): return ('H', i, j)
def Z(i): return ('Z', i)
def X(i, j): return ('X', i, j)


def diagram_route(left, right):
    # From the top left: down the left side, along H[0,1] at the bottom,
    # up the right side.  Operator order.
    path = list(left) + [H(0, 1)] + list(reversed(right))
    return list(reversed(path))


Z01 = [Z(0), Z(1)]
L20 = [H(0, 2), H(1, 3), H(0, 1)] + Z01 + [H(1, 3), H(0, 2)]
L30 = [H(0, 2), H(1, 3), H(0, 4), H(1, 5), H(0, 1)] + Z01 + [H(1, 5), H(0, 4), H(1, 3), H(0, 2)]
CORES = {'20': (diagram_route(L20, L20), 4), '30': (diagram_route(L30, L30), 6)}

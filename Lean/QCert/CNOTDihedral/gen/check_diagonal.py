"""Gadgets and diagonal normal forms (Gadget.lean, Diagonal.lean), checked
on phase-affine pairs.

* the words of R8, R9, R13 are the gadgets claimed (`P_U01'`, `P_V012`, ...);
* T0 U01 = U01 T0 and the steps of its proof (`qT0_comm_U01`);
* X conjugation of a gadget (`qX_conj_P`);
* the Moebius products m S have phase (-2)^(|S|-1) x_S (`phase_mob`),
  and orders 8, 4, 2 for |S| = 1, 2, 3 (`eight_mon`, `four_mon_two`,
  `two_mon_three`); for |S| >= 4 the phase vanishes, which is `R13`;
* the closure of the diagonal generators under CNOT conjugation stays within
  parities of at most four wires (`A_conj_lin`).
"""
import itertools
from sim import *


def g(n, *ws):
    return gadget(n, list(ws))


def check_words():
    n = 4
    U01 = cx(n, 0) * T(n, 0) * cx(n, 0)
    U12 = cx(n, 1) * T(n, 1) * cx(n, 1)
    U23 = cx(n, 2) * T(n, 2) * cx(n, 2)
    V012 = cx(n, 1) * cx(n, 0) * T(n, 0) * cx(n, 0) * cx(n, 1)
    V123 = cx(n, 2) * cx(n, 1) * T(n, 1) * cx(n, 1) * cx(n, 2)
    U02 = sw(n, 0) * U12 * sw(n, 0)
    U13 = sw(n, 1) * U23 * sw(n, 1)
    U03 = sw(n, 0) * sw(n, 1) * U23 * sw(n, 1) * sw(n, 0)
    V023 = sw(n, 0) * V123 * sw(n, 0)
    V013 = sw(n, 1) * sw(n, 0) * V123 * sw(n, 0) * sw(n, 1)
    L = cx(n, 2) * V012 * cx(n, 2)
    assert U01 == g(n, 0, 1) and U12 == g(n, 1, 2) and U23 == g(n, 2, 3)
    assert U02 == g(n, 0, 2) and U13 == g(n, 1, 3) and U03 == g(n, 0, 3)
    assert V012 == g(n, 0, 1, 2) and V123 == g(n, 1, 2, 3)
    assert V023 == g(n, 0, 2, 3) and V013 == g(n, 0, 1, 3)
    assert L == g(n, 0, 1, 2, 3)
    # R13 between gadgets (base_R13)
    rhs = (g(n, 0, 1, 2) * g(n, 0, 1, 3) * g(n, 0, 2, 3) * g(n, 1, 2, 3)
           * g(n, 0, 1) ** 3 * g(n, 0, 2) ** 3 * g(n, 1, 2) ** 3 * g(n, 0, 3) ** 3
           * g(n, 1, 3) ** 3 * g(n, 2, 3) ** 3
           * g(n, 3) ** 5 * g(n, 2) ** 5 * g(n, 1) ** 5 * g(n, 0) ** 5)
    assert L == rhs
    # R9, R8
    assert g(n, 0, 1, 2) ** 2 == (g(n, 0, 1) ** 2 * g(n, 0, 2) ** 2 * g(n, 1, 2) ** 2
                                  * g(n, 2) ** 6 * g(n, 1) ** 6 * g(n, 0) ** 6)
    assert g(n, 0, 1) ** 4 == g(n, 1) ** 4 * g(n, 0) ** 4
    print('R8, R9, R13 words and gadget forms: ok')


def check_T0_U01():
    n = 2
    U = cx(n, 0) * T(n, 0) * cx(n, 0)
    c01 = c(n, 0, 1)
    assert c01 == cx(n, 0) * sw(n, 0) * cx(n, 0)
    assert U == c01 * T(n, 1) * c01
    assert sw(n, 0) * U * sw(n, 0) == U
    assert T(n, 1) * U == U * T(n, 1)
    assert T(n, 0) * U == U * T(n, 0)
    print('T0 U01 = U01 T0 and its steps: ok')


def check_X_conj():
    n = 4
    for ws in [(0,), (0, 2), (1, 2, 3), (0, 1, 2, 3)]:
        for i in range(n):
            lhs = X(n, i) * g(n, *ws) * X(n, i)
            rhs = g(n, *ws) ** 7 * om(n) if i in ws else g(n, *ws)
            assert lhs == rhs
    print('X conjugation of gadgets: ok')


def mob(n, S):
    r = ident(n)
    for k in range(len(S) + 1):
        for W in itertools.combinations(S, k):
            if W:
                e = (-1) ** (len(S) - len(W)) % 8
                r = r * g(n, *W) ** e
    return r


def check_monomials():
    n = 5
    for k in range(1, 6):
        for S in itertools.combinations(range(n), k):
            m = mob(n, S)
            coef = (-2) ** (k - 1)
            want = mkop(n, lambda x: x, lambda x: coef * all(x[i] for i in S))
            assert m == want, S
            order = {1: 8, 2: 4, 3: 2}.get(k, 1)
            assert m ** order == ident(n)
    print('Moebius monomials, phases and orders (|S| <= 5): ok')


def check_closure():
    n = 5
    # conjugating the gadget of U by c(i+1, i) gives the gadget of U xor {i+1} if i in U
    for k in range(1, 4):
        for U in itertools.combinations(range(n), k):
            for i in range(n - 1):
                lhs = cx(n, i) * g(n, *U) * cx(n, i)
                V = set(U)
                if i in V:
                    V ^= {i + 1}
                assert lhs == g(n, *sorted(V)) and len(V) <= 4
                lhs = sw(n, i) * g(n, *U) * sw(n, i)
                W = sorted({(i + 1 if u == i else i if u == i + 1 else u) for u in U})
                assert lhs == g(n, *W)
    print('closure of the gadgets of at most three wires: ok')


check_words()
check_T0_U01()
check_X_conj()
check_monomials()
check_closure()

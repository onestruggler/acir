#!/usr/bin/env python3
"""Exact three-wire obstruction to decoding every Table 1 generator.

This is an independent finite invariant check, not a completeness proof.
Vectors represent twice a vector in the invariant set; all arithmetic is
integral.  Wire 0 is the least significant bit.  Run with Python 3.

The invariant is the union of the vectors with two entries in {+2,-2}
and six zero entries, and the {+1,-1} vectors with an even number of -1
entries.  It has 112 + 128 = 240 elements.  All requested three-wire
gates preserve it, whereas the ambient one-level sign and four-level K
generators need not.  Thus a semantics-preserving decoder for *all* of
CCX+HH-TwoLevel.Syntactics.Gen 8 cannot exist over three-wire circuits.
"""

from itertools import combinations, product
from fractions import Fraction


def invariant_vectors():
    vectors = set()
    for i, j in combinations(range(8), 2):
        for a, b in product((-2, 2), repeat=2):
            v = [0] * 8
            v[i], v[j] = a, b
            vectors.add(tuple(v))
    for v in product((-1, 1), repeat=8):
        if v.count(-1) % 2 == 0:
            vectors.add(v)
    return vectors


def controlled_x(v, target, controls=()):
    out = [0] * 8
    for i, entry in enumerate(v):
        j = i ^ (1 << target) if all(i & (1 << c) for c in controls) else i
        out[j] = entry
    return tuple(out)


def local_k(v, indices):
    """Apply the four-level normalized H tensor H on ordered indices."""
    out = list(v)
    for row, index in enumerate(indices):
        numerator = sum(
            (-1 if (row & col).bit_count() % 2 else 1) * v[j]
            for col, j in enumerate(indices)
        )
        if numerator % 2:
            raise ValueError("The claimed invariant has a nonintegral image")
        out[index] = numerator // 2
    return tuple(out)


def hh(v, a, b):
    remaining = next(i for i in range(3) if i not in (a, b))
    for bit in (0, 1):
        base = bit << remaining
        indices = [base | ((i & 1) << a) | ((i >> 1) << b) for i in range(4)]
        v = local_k(v, indices)
    return v


def check():
    vectors = invariant_vectors()
    assert len(vectors) == 240
    gates = []
    for target in range(3):
        others = [i for i in range(3) if i != target]
        gates.append((f"X{target}", lambda v, t=target: controlled_x(v, t)))
        for control in others:
            gates.append((f"CX{control}->{target}",
                          lambda v, t=target, c=control: controlled_x(v, t, (c,))))
        gates.append((f"CCX{others}->{target}",
                      lambda v, t=target, cs=tuple(others): controlled_x(v, t, cs)))
    for a, b in combinations(range(3), 2):
        gates.append((f"HH{a},{b}", lambda v, a=a, b=b: hh(v, a, b)))
    for name, action in gates:
        images = {action(v) for v in vectors}
        assert images == vectors, f"Invariant failure at {name}"

    witness = (1,) * 8
    sign_image = (-1,) + (1,) * 7
    k_image = local_k(witness, (0, 1, 2, 3))
    assert witness in vectors
    assert sign_image not in vectors
    assert k_image not in vectors
    # The invariant set spans R^8 (2e_i is half the sum of
    # 2e_i+2e_j and 2e_i-2e_j), so its permutation action is faithful:
    # the circuit subgroup is finite.  In contrast this ambient word
    # has trace 1/4.  A rational finite-order matrix has integer trace,
    # because its eigenvalues are roots of unity and its rational trace
    # is an algebraic integer.  Hence the ambient group is infinite.
    def k_matrix(indices):
        m = [[Fraction(i == j) for j in range(8)] for i in range(8)]
        for i, row in enumerate(indices):
            for j, col in enumerate(indices):
                m[row][col] = Fraction((-1) ** ((i & j).bit_count() % 2), 2)
        return m

    ka, kb = k_matrix((0, 1, 2, 3)), k_matrix((3, 4, 5, 6))
    trace = sum(ka[i][j] * kb[j][i] for i in range(8) for j in range(8))
    assert trace == Fraction(1, 4)
    print(f"PASS: {len(gates)} three-wire gates preserve {len(vectors)} vectors.")
    print(f"M[0] counterexample: {witness} -> {sign_image}")
    print(f"K[0,1,2,3] counterexample: {witness} -> {k_image}")
    print("No full-Table-1 generatorwise decoder exists at width three.")
    print(f"Ambient infinite-order witness K[0123] K[3456] has trace {trace}.")
    print("The three-wire circuit subgroup has infinite index in the ambient group.")


if __name__ == "__main__":
    check()

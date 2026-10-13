#!/usr/bin/env python3
"""Exact finite checks of the proposed all-width two-level encoding.

The independently constructed gate matrices use tensor/basis-vector
formulas.  Encoded words use the fixed 2-level X and 4-level K matrices.
Fractions are exact.  These checks are evidence for, not a replacement
for, an Agda semantic-correctness theorem at symbolic width.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction


ZERO = Fraction(0)
ONE = Fraction(1)
HALF = Fraction(1, 2)
K_SIGNS = ((1, 1, 1, 1), (1, -1, 1, -1),
           (1, 1, -1, -1), (1, -1, -1, 1))


def identity(n):
    size = 1 << n
    return [[ONE if r == c else ZERO for c in range(size)]
            for r in range(size)]


def encoding(n, gate):
    """Same block choice as Encoding.agda, without Fin conversions."""
    kind, *wires = gate
    if kind == "HH":
        p, q = sorted(wires)
        return [("K", a, a + (1 << p), a + (1 << q),
                 a + (1 << p) + (1 << q))
                for a in range(1 << n)
                if not a & (1 << p) and not a & (1 << q)]
    *controls, target = wires
    return [("X", a, a + (1 << target))
            for a in range(1 << n)
            if not a & (1 << target)
            and all(a & (1 << control) for control in controls)]


def two_level_matrix(n, word):
    matrix = identity(n)
    # Words denote matrix products in written order.
    for kind, *indices in reversed(word):
        if kind == "X":
            a, b = indices
            matrix[a], matrix[b] = matrix[b], matrix[a]
        elif kind == "K":
            old = [matrix[i] for i in indices]
            for i, signs in zip(indices, K_SIGNS):
                matrix[i] = [sum((sign * row[c]
                                  for sign, row in zip(signs, old)), ZERO) * HALF
                             for c in range(1 << n)]
        else:
            raise ValueError(kind)
    return matrix


def gate_matrix(n, gate):
    """Direct basis-vector semantics, independent of level encoding."""
    size = 1 << n
    matrix = [[ZERO for _ in range(size)] for _ in range(size)]
    kind, *wires = gate
    if kind == "HH":
        p, q = wires
        mask = (1 << p) | (1 << q)
        for col in range(size):
            for bp, bq in itertools.product(range(2), repeat=2):
                row = (col & ~mask) | (bp << p) | (bq << q)
                exponent = bp * ((col >> p) & 1) + bq * ((col >> q) & 1)
                matrix[row][col] = -HALF if exponent % 2 else HALF
    else:
        *controls, target = wires
        for col in range(size):
            activated = all((col >> c) & 1 for c in controls)
            row = col ^ ((1 << target) if activated else 0)
            matrix[row][col] = ONE
    return matrix


def multiply(a, b):
    size = len(a)
    out = [[ZERO for _ in range(size)] for _ in range(size)]
    for r, row in enumerate(a):
        for k, value in enumerate(row):
            if value:
                for c, value_b in enumerate(b[k]):
                    if value_b:
                        out[r][c] += value * value_b
    return out


def circuit_matrix(n, gates):
    result = identity(n)
    for gate in gates:
        result = multiply(result, gate_matrix(n, gate))
    return result


def all_gates(n):
    for target in range(n):
        yield ("X", target)
        for control in range(n):
            if control != target:
                yield ("CX", control, target)
        for c, d in itertools.combinations((i for i in range(n) if i != target), 2):
            yield ("CCX", c, d, target)
    for p, q in itertools.combinations(range(n), 2):
        yield ("HH", p, q)


def verify(max_width):
    count = 0
    by_width = {}
    shortcuts = 0
    for n in range(max_width + 1):
        at_width = 0
        for gate in all_gates(n):
            assert gate_matrix(n, gate) == two_level_matrix(n, encoding(n, gate)), (n, gate)
            count += 1
            at_width += 1
        by_width[str(n)] = at_width
        if n >= 2:
            hh, cx, x = ("HH", 0, 1), ("CX", 1, 0), ("X", 0)
            assert circuit_matrix(n, [hh, cx, hh]) == gate_matrix(n, ("CX", 0, 1))
            swap = circuit_matrix(n, [cx, hh, cx, hh, cx])
            expected_swap = [[ZERO for _ in range(1 << n)] for _ in range(1 << n)]
            for col in range(1 << n):
                row = (col & ~3) | ((col & 1) << 1) | ((col & 2) >> 1)
                expected_swap[row][col] = ONE
            assert swap == expected_swap
            z = [hh, x, hh]
            expected_z = [[(-ONE if r & 1 else ONE) if r == c else ZERO
                           for c in range(1 << n)] for r in range(1 << n)]
            assert circuit_matrix(n, z) == expected_z
            assert circuit_matrix(n, [x] + z + [x] + z) == [
                [-entry for entry in row] for row in identity(n)]
            shortcuts += 4
    return {
        "arithmetic": "fractions.Fraction (exact)",
        "max_width": max_width,
        "gate_encodings_checked": count,
        "checks_by_width": by_width,
        "derived_shortcuts_checked": shortcuts,
        "scope": "Finite checks; symbolic-width semantic preservation is not yet proved.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=5)
    args = parser.parse_args()
    if not 0 <= args.max_width <= 8:
        parser.error("--max-width must be between 0 and 8")
    print(json.dumps(verify(args.max_width), indent=2))

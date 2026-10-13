#!/usr/bin/env python3
"""Exact gate arithmetic and finite base-case diagnostics.

The group enumeration checks subgroup sizes before constructing Clément's
translation.  It does not supply an alternative circuit presentation.

Matrices are integer numerators divided by sqrt(2)**exponent.  No floating
point operations, numerical tolerances, or third-party packages are used.
Wire 0 is the least significant bit; words are in matrix product order.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from itertools import combinations, permutations
import json
from pathlib import Path


@dataclass(frozen=True)
class Matrix:
    exponent: int
    entries: tuple[int, ...]


Gate = tuple[str, tuple[int, ...]]


def canonical(exponent: int, entries: tuple[int, ...]) -> Matrix:
    while exponent >= 2 and all(x % 2 == 0 for x in entries):
        exponent -= 2
        entries = tuple(x // 2 for x in entries)
    return Matrix(exponent, entries)


def identity(n: int) -> Matrix:
    dim = 1 << n
    return Matrix(0, tuple(int(r == c) for r in range(dim) for c in range(dim)))


def alphabet(n: int, gate_set: str) -> list[Gate]:
    result: list[Gate] = [("X", (t,)) for t in range(n)]
    result += [("CX", (c, t)) for c, t in permutations(range(n), 2)]
    result += [("CCX", (a, b, t)) for a, b in combinations(range(n), 2)
               for t in range(n) if t not in (a, b)]
    if gate_set == "HH":
        result += [("HH", (a, b)) for a, b in combinations(range(n), 2)]
    elif gate_set == "H":
        result += [("H", (t,)) for t in range(n)]
    else:
        raise ValueError(gate_set)
    return result


def append_gate(a: Matrix, gate: Gate, n: int) -> Matrix:
    """Right multiplication by a gate, implemented as column operations."""
    kind, wires = gate
    dim = 1 << n
    if kind in ("H", "HH"):
        entries = a.entries
        for wire in wires:
            out = list(entries)
            mask = 1 << wire
            for r in range(dim):
                for c in range(dim):
                    if not c & mask:
                        p, q = r * dim + c, r * dim + (c | mask)
                        out[p], out[q] = entries[p] + entries[q], entries[p] - entries[q]
            entries = tuple(out)
        return canonical(a.exponent + len(wires), entries)
    controls, target = wires[:-1], wires[-1]
    perm = [c ^ (1 << target) if all(c & (1 << w) for w in controls) else c
            for c in range(dim)]
    return canonical(a.exponent, tuple(a.entries[r * dim + perm[c]]
                                     for r in range(dim) for c in range(dim)))


def evaluate(word: tuple[int, ...], gates: list[Gate], n: int) -> Matrix:
    value = identity(n)
    for g in word:
        value = append_gate(value, gates[g], n)
    return value


def enumerate_group(n: int, gate_set: str, limit: int = 10000) -> dict:
    if not 0 <= n <= 2:
        raise ValueError("Exhaustive enumeration is deliberately restricted to 0, 1, 2 wires")
    gates = alphabet(n, gate_set)
    matrices = [identity(n)]
    ids = {matrices[0]: 0}
    words: list[tuple[int, ...]] = [()]
    queue = deque([0])
    edges: list[list[int]] = []
    while queue:
        state = queue.popleft()
        row = []
        for g, gate in enumerate(gates):
            b = append_gate(matrices[state], gate, n)
            if b not in ids:
                if len(matrices) >= limit:
                    raise RuntimeError("State limit reached; no completeness claim can be made")
                ids[b] = len(matrices)
                matrices.append(b)
                words.append(words[state] + (g,))
                queue.append(ids[b])
            row.append(ids[b])
        edges.append(row)
    # Independently reconstruct each advertised representative and check
    # each edge, involution, and matrix orthogonality with integer arithmetic.
    for state, (a, word) in enumerate(zip(matrices, words)):
        assert evaluate(word, gates, n) == a
        dim = 1 << n
        for r in range(dim):
            for s in range(dim):
                inner = sum(a.entries[r * dim + c] * a.entries[s * dim + c]
                            for c in range(dim))
                assert inner == ((1 << a.exponent) if r == s else 0)
        for g, gate in enumerate(gates):
            target = edges[state][g]
            assert append_gate(a, gate, n) == matrices[target]
            assert edges[target][g] == state
    return {
        "format": "ccx-finite-group-diagnostic-v1",
        "gate_set": ["X", "CX", "CCX", gate_set],
        "wires": n,
        "wire_order": "least-significant-bit first",
        "word_order": "matrix product order",
        "order": len(matrices),
        "generators": [{"gate": kind, "wires": list(wires)} for kind, wires in gates],
        "representatives": [list(w) for w in words],
        "transitions": edges,
        "maximum_normal_form_length": max(map(len, words)),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate-set", choices=("HH", "H", "both"), default="both")
    parser.add_argument("--wires", type=int, choices=(0, 1, 2))
    parser.add_argument("--output", type=Path, help="Write full transition tables as JSON")
    args = parser.parse_args()
    gate_sets = ("HH", "H") if args.gate_set == "both" else (args.gate_set,)
    widths = range(3) if args.wires is None else (args.wires,)
    results = [enumerate_group(n, gs) for gs in gate_sets for n in widths]
    for result in results:
        print(f"{result['gate_set'][-1]} n={result['wires']}: "
              f"{result['order']} matrices, "
              f"maximum normal form length {result['maximum_normal_form_length']}; verified")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

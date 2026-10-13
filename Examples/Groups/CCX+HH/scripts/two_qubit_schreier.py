#!/usr/bin/env python3
"""Derive a complete two-qubit circuit presentation by Clément's method.

The ambient presentation is exactly CCX+HH-TwoLevel/Syntactics.agda at
matrix dimension 4 (Li--Ross--Selinger Table 1).  Enumerating exact matrices
finds three right cosets of the circuit subgroup in the ambient group.
Its Schreier decoder transports every ambient relator at every coset;
generator roundtrips provide the back-and-forth retraction.  No Coxeter
presentation or external circuit relation list is used.

The resulting finite circuit relations are sound and complete by the
repository's Reidemeister--Schreier theorem.  The concrete table, state
obligations, all 33 factorizations, and the bridge to independent circuit
matrices are proved in TwoQubit/Presentation.agda and its imports.  This
program independently reproduces the table and checks every resulting
equation with exact arithmetic; Agda verifies the formal proof separately.
"""

from __future__ import annotations

import argparse
from collections import deque
from itertools import combinations
import json
from pathlib import Path

from exact_matrices import Matrix, canonical, identity, append_gate, evaluate


DIM = 4
CIRCUIT_GATES = [("X", (0,)), ("X", (1,)), ("CX", (1, 0)), ("HH", (0, 1))]
AMBIENT_GATES = ([('M', a) for a in range(DIM)]
                 + [('X', a, b) for a, b in combinations(range(DIM), 2)]
                 + [('K', 0, 1, 2, 3)])
AID = {g: i for i, g in enumerate(AMBIENT_GATES)}


def multiply(a, b):
    return canonical(a.exponent + b.exponent, tuple(
        sum(a.entries[r * DIM + k] * b.entries[k * DIM + c] for k in range(DIM))
        for r in range(DIM) for c in range(DIM)))


def transpose(a):
    return Matrix(a.exponent, tuple(a.entries[c * DIM + r]
                                   for r in range(DIM) for c in range(DIM)))


def ambient_matrix(g):
    entries = list(identity(2).entries)
    kind, *levels = g
    if kind == 'M':
        a, = levels
        entries[a * DIM + a] = -1
        return Matrix(0, tuple(entries))
    if kind == 'X':
        a, b = levels
        entries[a * DIM + a] = entries[b * DIM + b] = 0
        entries[a * DIM + b] = entries[b * DIM + a] = 1
        return Matrix(0, tuple(entries))
    if kind == 'K':
        return Matrix(2, (1, 1, 1, 1, 1, -1, 1, -1,
                          1, 1, -1, -1, 1, -1, -1, 1))
    raise ValueError(g)


AMATS = [ambient_matrix(g) for g in AMBIENT_GATES]


def value(word, matrices):
    result = identity(2)
    for i in word:
        result = multiply(result, matrices[i])
    return result


def enumerate_closed(matrices, limit):
    seen = {identity(2): ()}
    queue = deque([identity(2)])
    while queue:
        a = queue.popleft()
        for i, g in enumerate(matrices):
            b = multiply(a, g)
            if b not in seen:
                if len(seen) >= limit:
                    raise RuntimeError("Enumeration bound exceeded; no certificate produced")
                seen[b] = seen[a] + (i,)
                queue.append(b)
    for a, word in seen.items():
        assert value(word, matrices) == a
        assert multiply(a, transpose(a)) == identity(2)
    return seen


def ambient_relations():
    """All and only well-formed Table 1 instances in dimension four."""
    result = []

    def add(name, left, right):
        result.append({"source": name, "left": [AID[g] for g in left],
                       "right": [AID[g] for g in right]})

    pairs = list(combinations(range(DIM), 2))
    for a, b in pairs:
        x = ('X', a, b)
        add(f'r1a[{a},{b}]', [x, x], [])
    for a in range(DIM):
        m = ('M', a)
        add(f'r1b[{a}]', [m, m], [])
    k = ('K', 0, 1, 2, 3)
    add('r1c[0,1,2,3]', [k, k], [])
    for a, b in pairs:
        x = ('X', a, b)
        for c, d in pairs:
            if not {a, b} & {c, d}:
                y = ('X', c, d)
                add(f'r2a[{a},{b},{c},{d}]', [x, y], [y, x])
        for c in range(DIM):
            if c not in (a, b):
                m = ('M', c)
                add(f'r2b[{a},{b},{c}]', [x, m], [m, x])
    for a in range(DIM):
        for b in range(DIM):
            if a != b:
                ma, mb = ('M', a), ('M', b)
                add(f'r2d[{a},{b}]', [ma, mb], [mb, ma])
    for a, b, c in combinations(range(DIM), 3):
        ab, ac, bc = ('X', a, b), ('X', a, c), ('X', b, c)
        add(f'r3a[{a},{b},{c}]', [ab, ac], [bc, ab])
        add(f'r3b[{a},{b},{c}]', [bc, ab], [ac, bc])
    for a, b in pairs:
        x = ('X', a, b)
        add(f'r3c[{a},{b}]', [x, ('M', b)], [('M', a), x])
    add('r4a[0,1,2,3]', [('X', 0, 1), k], [k, ('X', 1, 3), ('M', 1), ('M', 3)])
    add('r4b[0,1,2,3]', [('X', 1, 2), k], [('M', 0), k, ('M', 0), k, ('M', 0)])
    add('r4c[0,1,2,3]', [('X', 2, 3), k], [k, ('X', 1, 3)])
    assert len(result) == 58
    for relation in result:
        assert value(relation['left'], AMATS) == value(relation['right'], AMATS), relation
    return result


def generate():
    circuit_matrices = [append_gate(identity(2), g, 2) for g in CIRCUIT_GATES]
    subgroup = enumerate_closed(circuit_matrices, 2000)
    ambient = enumerate_closed(AMATS, 2000)
    assert len(subgroup) == 384
    assert len(ambient) == 1152
    assert all(a in ambient for a in subgroup)

    # H r_c are right cosets.  Thus r_c y = h(c,y) r_c'.
    representatives = []
    coset_of = {}
    for r in ambient:
        if r not in coset_of:
            c = len(representatives)
            representatives.append(r)
            for h in subgroup:
                hr = multiply(h, r)
                assert hr not in coset_of
                coset_of[hr] = c
    assert len(representatives) == 3 and len(coset_of) == 1152
    assert representatives[0] == identity(2)

    table = []
    for r in representatives:
        row = []
        for y in AMATS:
            ry = multiply(r, y)
            c = coset_of[ry]
            h = multiply(ry, transpose(representatives[c]))
            assert h in subgroup
            word = subgroup[h]
            assert multiply(value(word, circuit_matrices), representatives[c]) == ry
            row.append({"word": list(word), "state": c})
        table.append(row)

    def decode(c, word):
        out = []
        for y in word:
            cell = table[c][y]
            out.extend(cell['word'])
            c = cell['state']
        return out, c

    axioms = ambient_relations()
    relations = []
    for c in range(3):
        for axiom in axioms:
            left, lc = decode(c, axiom['left'])
            right, rc = decode(c, axiom['right'])
            assert lc == rc
            assert value(left, circuit_matrices) == value(right, circuit_matrices)
            relations.append({"source": axiom['source'], "coset": c,
                              "left": left, "right": right})
    encoded = [[AID[('X', 0, 1)], AID[('X', 2, 3)]],
               [AID[('X', 0, 2)], AID[('X', 1, 3)]],
               [AID[('X', 2, 3)]], [AID[('K', 0, 1, 2, 3)]]]
    for i, word in enumerate(encoded):
        assert value(word, AMATS) == circuit_matrices[i]
        decoded, end = decode(0, word)
        assert end == 0
        assert value(decoded, circuit_matrices) == circuit_matrices[i]
        relations.append({"source": f'roundtrip[{i}]', "left": [i], "right": decoded})

    # Further check the stateful encoder/decoder on every circuit normal
    # form, including its semantics and return to the subgroup coset.
    for a, word in subgroup.items():
        encoded_word = [y for g in word for y in encoded[g]]
        decoded, end = decode(0, encoded_word)
        assert end == 0 and value(decoded, circuit_matrices) == a

    return {
        "format": "clement-schreier-circuit-presentation-v1",
        "wires": 2,
        "arithmetic": "integer numerators / sqrt(2)^exponent, canonical",
        "word_order": "matrix product order",
        "wire_order": "wire 0 is least significant",
        "source": "Examples/Groups/CCX+HH-TwoLevel/Syntactics.agda, Table 1 at N=4",
        "method": "right-coset Schreier decoding, translated source axioms, generator roundtrips",
        "ambient_order": len(ambient), "subgroup_order": len(subgroup),
        "coset_count": len(representatives),
        "circuit_generators": [{"gate": g, "wires": list(w)} for g, w in CIRCUIT_GATES],
        "auxiliary_generators": [{"gate": g[0], "levels": list(g[1:])} for g in AMBIENT_GATES],
        "generator_encodings": encoded,
        "coset_representatives": [list(ambient[r]) for r in representatives],
        "schreier_table": table,
        "auxiliary_relations": axioms,
        "circuit_relations": relations,
        "verification": {
            "auxiliary_axioms_checked": len(axioms),
            "table_factorizations_checked": len(representatives) * len(AMATS),
            "state_relations_checked": len(representatives) * len(axioms),
            "roundtrips_checked": len(encoded),
            "subgroup_normal_forms_checked": len(subgroup),
            "all_output_relations_checked": len(relations),
            "agda_instantiation": "TwoQubit/Presentation.agda: soundness and completeness checked with Agda 2.8.0",
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path, help='Rebuild and compare an existing artifact')
    args = parser.parse_args()
    result = generate()
    if args.check:
        assert json.loads(args.check.read_text(encoding='utf8')) == result
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf8')
    print(json.dumps({key: result[key] for key in
                      ('ambient_order', 'subgroup_order', 'coset_count', 'verification')}, indent=2))


if __name__ == '__main__':
    main()

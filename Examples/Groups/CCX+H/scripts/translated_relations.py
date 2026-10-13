#!/usr/bin/env python3
"""Export explicit H1/H2/H3 circuit relations using Clément translation.

Only the auxiliary relations in CCX+HH-TwoLevel/Syntactics.agda and
Scaled/Syntactics.agda are used.  Every legal index instance is included,
then decoded gate by gate using the repository's concrete decoders.  The
gate encode/decode roundtrips complete the back-and-forth presentation.

Verification checks every decoder image, every source equation, and every
roundtrip with exact integer arithmetic.  Decoding is a word homomorphism,
so source equality and the checked generator images imply soundness of
every exported circuit equation without repeatedly evaluating long words.
The corresponding Agda presentations supply the completeness proof.
"""

from __future__ import annotations

import argparse
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
HH_SCRIPTS = HERE.parent.parent / 'CCX+HH' / 'scripts'
sys.path.insert(0, str(HH_SCRIPTS))
from exact_matrices import Matrix, canonical, identity, append_gate, evaluate


def source_relations(size):
    """All Table 1 and scaled Table 2 instances, zero-based indices."""
    relations = []
    pairs = list(combinations(range(size), 2))
    quads = list(combinations(range(size), 4))
    m = lambda a: ('M', a)
    x = lambda a, b: ('X', a, b)
    k = lambda *indices: ('K', *indices)
    ih = ('IH',)

    def add(rule, indices, left, right):
        relations.append((rule, list(indices), left, right))

    for a, b in pairs:
        add('r1a', (a, b), [x(a, b)] * 2, [])
    for a in range(size):
        add('r1b', (a,), [m(a)] * 2, [])
    for q in quads:
        add('r1c', q, [k(*q)] * 2, [])
    for (a, b), (c, d) in product(pairs, repeat=2):
        if not {a, b} & {c, d}:
            add('r2a', (a, b, c, d), [x(a, b), x(c, d)], [x(c, d), x(a, b)])
    for a, b in pairs:
        for c in range(size):
            if c not in (a, b):
                add('r2b', (a, b, c), [x(a, b), m(c)], [m(c), x(a, b)])
        for q in quads:
            if not {a, b} & set(q):
                add('r2c', (a, b, *q), [x(a, b), k(*q)], [k(*q), x(a, b)])
    for a, b in product(range(size), repeat=2):
        if a != b:
            add('r2d', (a, b), [m(a), m(b)], [m(b), m(a)])
    for a in range(size):
        for q in quads:
            if a not in q:
                add('r2e', (a, *q), [m(a), k(*q)], [k(*q), m(a)])
    for q, r in product(quads, repeat=2):
        if not set(q) & set(r):
            add('r2f', (*q, *r), [k(*q), k(*r)], [k(*r), k(*q)])
    for a, b, c in combinations(range(size), 3):
        add('r3a', (a, b, c), [x(a, b), x(a, c)], [x(b, c), x(a, b)])
        add('r3b', (a, b, c), [x(b, c), x(a, b)], [x(a, c), x(b, c)])
    for a, b in pairs:
        add('r3c', (a, b), [x(a, b), m(b)], [m(a), x(a, b)])
    for a, b, c, d, e in combinations(range(size), 5):
        add('r3d', (a, b, c, d, e), [x(a, b), k(a, c, d, e)], [k(b, c, d, e), x(a, b)])
        add('r3e', (a, b, c, d, e), [x(b, c), k(a, b, d, e)], [k(a, c, d, e), x(b, c)])
        add('r3f', (a, b, c, d, e), [x(c, d), k(a, b, c, e)], [k(a, b, d, e), x(c, d)])
        add('r3g', (a, b, c, d, e), [x(d, e), k(a, b, c, d)], [k(a, b, c, e), x(d, e)])
    for a, b, c, d in quads:
        q = k(a, b, c, d)
        add('r4a', (a, b, c, d), [x(a, b), q], [q, x(b, d), m(b), m(d)])
        add('r4b', (a, b, c, d), [x(b, c), q], [m(a), q, m(a), q, m(a)])
        add('r4c', (a, b, c, d), [x(c, d), q], [q, x(b, d)])
    for a, b, c, d, e, f in combinations(range(size), 6):
        add('r5a', (a, b, c, d, e, f), [k(a, b, c, d), k(b, d, e, f)],
            [k(c, d, e, f), k(a, b, c, e)])
    for a, b, c, d, e, f, g, h in combinations(range(size), 8):
        left = [m(a), m(e), x(a, e), k(e, f, g, h), k(a, b, c, d), x(d, e),
                k(a, b, c, d), k(e, f, g, h), x(a, e), m(a), m(e)]
        right = [k(e, f, g, h), k(a, b, c, d), x(d, e), k(a, b, c, d), k(e, f, g, h)]
        add('r6a', (a, b, c, d, e, f, g, h), left, right)
    table1_count = len(relations)
    assert table1_count == {2: 6, 4: 58, 8: 2123}[size]
    add('r7a', (), [ih, ih], [])
    if size >= 4:
        add('r7b', (0, 1, 2, 3), [ih, k(0, 1, 2, 3), ih], [k(0, 1, 2, 3)])
    add('r7c', (0, 1), [ih, m(0), ih], [m(0), x(0, 1), m(0)])
    for a in range(size - 1):
        if a % 2 == 0:
            add('r7d-even', (a, a + 1), [ih, x(a, a + 1), ih], [m(a + 1)])
        else:
            add('r7d-odd', (a - 1, a, a + 1, a + 2),
                [ih, x(a, a + 1), ih], [x(a, a + 1), k(a - 1, a, a + 1, a + 2)])
    return relations, table1_count


def circuit_generators(n):
    return ([('X', (p,)) for p in range(n)]
            + [('CX', (p + 1, p)) for p in range(n - 1)]
            + [('CCX', (p + 1, p + 2, p)) for p in range(n - 2)]
            + [('H', (p,)) for p in range(n)])


def decoder(n):
    if n == 1:
        x0, h0 = [('X', (0,))], [('H', (0,))]
        images = {('M', 0): x0 + h0 + x0 + h0 + x0,
                  ('M', 1): h0 + x0 + h0, ('X', 0, 1): x0, ('IH',): h0}
        return images.__getitem__
    if n == 3:
        path = HERE.parent / 'ThreeQubit' / 'build_decoding.py'
        spec = importlib.util.spec_from_file_location('h3_decoder', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        def decode(g):
            kind, *indices = g
            raw = (module.sign(indices[0]) if kind == 'M' else
                   module.exchange(*indices) if kind == 'X' else
                   module.four(tuple(indices)) if kind == 'K' else module.h(0))
            return [(gate[0].upper(), tuple(gate[1:])) for gate in raw]
        return decode

    # Literal expansion of TwoQubit/Decoding.agda.
    x0, x1 = [('X', (0,))], [('X', (1,))]
    h0, h1 = [('H', (0,))], [('H', (1,))]
    c10 = [('CX', (1, 0))]
    c01 = h0 + h1 + c10 + h0 + h1
    cz = h0 + c10 + h0
    signs = [x0 + x1 + cz + x1 + x0, x1 + cz + x1, x0 + cz + x0, cz]
    x01 = x1 + c10 + x1
    exchanges = {(0, 1): x01, (0, 2): x0 + c01 + x0,
                 (0, 3): x01 + c01 + x01, (1, 2): c10 + c01 + c10,
                 (1, 3): c01, (2, 3): c10}

    def decode(g):
        kind, *indices = g
        return (signs[indices[0]] if kind == 'M' else exchanges[tuple(indices)] if kind == 'X'
                else h0 + h1 if kind == 'K' else h0)
    return decode


def auxiliary_matrix(n, g):
    size = 1 << n
    kind, *indices = g
    if kind == 'IH':
        return append_gate(identity(n), ('H', (0,)), n)
    entries = list(identity(n).entries)
    if kind == 'M':
        a, = indices
        entries[a * size + a] = -1
        return Matrix(0, tuple(entries))
    if kind == 'X':
        a, b = indices
        entries[a * size + a] = entries[b * size + b] = 0
        entries[a * size + b] = entries[b * size + a] = 1
        return Matrix(0, tuple(entries))
    entries = [2 * v for v in entries]
    for r, a in enumerate(indices):
        for c, b in enumerate(indices):
            entries[a * size + b] = -1 if (r & c).bit_count() % 2 else 1
    return Matrix(2, tuple(entries))


def multiply(n, a, b):
    size = 1 << n
    return canonical(a.exponent + b.exponent, tuple(
        sum(a.entries[r * size + k] * b.entries[k * size + c] for k in range(size))
        for r in range(size) for c in range(size)))


def encode_generator(n, gate):
    kind, wires = gate
    if kind == 'H':
        p, = wires
        swaps = [('X', a, a + (1 << p) - 1) for a in range(1 << n)
                 if a & 1 and not a & (1 << p)] if p else []
        return swaps + [('IH',)] + swaps
    *controls, target = wires
    return [('X', a, a + (1 << target)) for a in range(1 << n)
            if not a & (1 << target) and all(a & (1 << c) for c in controls)]


def generate(n):
    size = 1 << n
    gates = circuit_generators(n)
    gid = {g: i for i, g in enumerate(gates)}
    auxiliary = ([('M', a) for a in range(size)]
                 + [('X', a, b) for a, b in combinations(range(size), 2)]
                 + [('K', *q) for q in combinations(range(size), 4)] + [('IH',)])
    aid = {g: i for i, g in enumerate(auxiliary)}
    decode = decoder(n)
    decoded = {g: [gid[x] for x in decode(g)] for g in auxiliary}
    matrices = {g: auxiliary_matrix(n, g) for g in auxiliary}
    for g in auxiliary:
        assert evaluate(tuple(decoded[g]), gates, n) == matrices[g], ('decoder', g)

    def source_value(word):
        result = identity(n)
        for g in word:
            result = multiply(n, result, matrices[g])
        return result

    relations, count1 = source_relations(size)
    output = []
    for rule, indices, left, right in relations:
        assert source_value(left) == source_value(right), (rule, indices)
        output.append({"source": rule, "indices": indices,
                       "auxiliary_left": [aid[g] for g in left],
                       "auxiliary_right": [aid[g] for g in right],
                       "left": [x for g in left for x in decoded[g]],
                       "right": [x for g in right for x in decoded[g]]})
    for i, gate in enumerate(gates):
        encoded = encode_generator(n, gate)
        back = [x for g in encoded for x in decoded[g]]
        expected = append_gate(identity(n), gate, n)
        assert source_value(encoded) == expected
        assert evaluate(tuple(back), gates, n) == expected
        output.append({"source": "roundtrip", "generator": i,
                       "auxiliary_encoding": [aid[g] for g in encoded], "left": [i], "right": back})
    assert len(output) == {1: 11, 2: 69, 3: 2142}[n]
    theorem = {1: 'OneQubit.agda', 2: 'TwoQubit.agda', 3: 'ThreeQubit/Presentation.agda'}[n]
    return {"format": "clement-translated-circuit-presentation-v1", "wires": n,
            "word_order": "matrix product order", "wire_order": "wire 0 is least significant",
            "sources": ["CCX+HH-TwoLevel/Syntactics.agda", "CCX+HH-TwoLevel/Scaled/Syntactics.agda"],
            "method": "decode every auxiliary relation and add circuit generator roundtrips",
            "circuit_generators": [{"gate": g, "wires": list(w)} for g, w in gates],
            "auxiliary_generators": [{"gate": g[0], "levels": list(g[1:])} for g in auxiliary],
            "decoder": [decoded[g] for g in auxiliary], "relations": output,
            "verification": {"arithmetic": "exact integer numerators / sqrt(2)^exponent",
                             "decoder_images": len(auxiliary), "table1_instances": count1,
                             "table2_instances": len(relations) - count1,
                             "roundtrips": len(gates), "circuit_relations": len(output),
                             "soundness": "checked decoder images + every source equation + roundtrips",
                             "completeness": f"Agda: CCX+H/{theorem}"}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wires', type=int, choices=(1, 2, 3), required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = generate(args.wires)
    if args.check:
        assert json.loads(args.check.read_text(encoding='utf8')) == result
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        # One equation per line, with compact word arrays, makes the large
        # relation list readable without expanding every gate to a line.
        metadata = {key: value for key, value in result.items() if key != 'relations'}
        rendered = json.dumps(metadata, indent=2)[:-2] + ',\n  "relations": [\n'
        rendered += ',\n'.join('    ' + json.dumps(relation, separators=(',', ':'))
                               for relation in result['relations'])
        rendered += '\n  ]\n}\n'
        args.output.write_text(rendered, encoding='utf8')
    print(json.dumps(result['verification'], indent=2))


if __name__ == '__main__':
    main()

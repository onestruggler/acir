#!/usr/bin/env python3
"""Exact finite coset diagnostic for the three-wire CCX+HH image.

This uses only the eight adjacent circuit generators and elementary
integer arithmetic.  It does not import a presentation of an exceptional
reflection group.  The preserved 240-vector set comes from check_subgroup.

The orbit of the unoriented coordinate frame gives the index of its
stabilizer.  That stabilizer is the even signed permutation group: the
root invariant gives the upper bound, and fourteen explicitly verified
circuit words generate it.  Thus orbit-stabilizer computes the full
circuit group order without enumerating its elements.

Words in this diagnostic apply their gates from left to right.  Reversing
such a list gives the repository's matrix-order circuit word.  All gates
are involutions.  This file is a finite diagnostic, not an Agda proof or
a complete circuit presentation.
"""

from functools import lru_cache
from heapq import heappop, heappush
from itertools import combinations
from math import factorial
from pathlib import Path
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_subgroup import controlled_x, hh, invariant_vectors


NAMES = ("X0", "X1", "X2", "CX10", "CX21", "CCX210", "HH01", "HH12")
BASIS = tuple(tuple(4 * (i == j) for i in range(8)) for j in range(8))


@lru_cache(maxsize=None)
def gate(name, vector):
    if name.startswith("X"):
        return controlled_x(vector, int(name[1]))
    if name == "CX10":
        return controlled_x(vector, 0, (1,))
    if name == "CX21":
        return controlled_x(vector, 1, (2,))
    if name == "CCX210":
        return controlled_x(vector, 0, (1, 2))
    if name == "HH01":
        return hh(vector, 0, 1)
    if name == "HH12":
        return hh(vector, 1, 2)
    raise ValueError(name)


def apply_word(vector, word):
    for name in word:
        vector = gate(name, vector)
    return vector


def canonical_frame(vectors):
    """Forget column order and the sign of each column, exactly."""
    result = []
    for vector in vectors:
        first = next(x for x in vector if x)
        result.append(vector if first > 0 else tuple(-x for x in vector))
    return tuple(sorted(result))


def frame_orbit():
    initial = canonical_frame(BASIS)
    frames, words = [initial], [()]
    numbers = {initial: 0}
    transitions = []
    for frame, word in zip(frames, words):
        row = []
        for name in NAMES:
            image = canonical_frame(gate(name, vector) for vector in frame)
            if image not in numbers:
                numbers[image] = len(frames)
                frames.append(image)
                words.append(word + (name,))
            row.append(numbers[image])
        transitions.append(row)
    # Every stored representative reaches its frame; all transitions
    # form a closed orbit under precisely the requested generators.
    for frame, word in zip(frames, words):
        assert canonical_frame(apply_word(v, word) for v in BASIS) == frame
        for u in frame:
            assert sum(x * x for x in u) == 16
        for u, v in combinations(frame, 2):
            assert sum(x * y for x, y in zip(u, v)) == 0
    for row in transitions:
        assert all(0 <= x < len(frames) for x in row)
    return frames, words, transitions


def classical_macros():
    # Both directions of adjacent CNOT suffice for affine routing.
    result = [((f"X{t}",), lambda i, t=t: i ^ (1 << t)) for t in range(3)]
    for control, target, word in (
        (1, 0, ("CX10",)),
        (2, 1, ("CX21",)),
        (0, 1, ("HH01", "CX10", "HH01")),
        (1, 2, ("HH12", "CX21", "HH12")),
    ):
        action = lambda i, c=control, t=target: i ^ (1 << t) if i & (1 << c) else i
        result.append((word, action))
        for i, vector in enumerate(BASIS):
            assert apply_word(vector, word) == BASIS[action(i)]
    return result


def exchange_words():
    """Conjugate the native (6,7) exchange to every pair of basis levels."""
    routes = {(6, 7): ()}
    queue = [(0, (6, 7))]
    macros = classical_macros()
    while queue:
        cost, pair = heappop(queue)
        if cost != len(routes[pair]):
            continue
        for word, action in macros:
            image = tuple(sorted(action(i) for i in pair))
            if image not in routes or cost + len(word) < len(routes[image]):
                routes[image] = routes[pair] + word
                heappush(queue, (cost + len(word), image))
    assert len(routes) == 28
    result = {}
    for pair, route in routes.items():
        word = tuple(reversed(route)) + ("CCX210",) + route
        a, b = pair
        for i, vector in enumerate(BASIS):
            j = b if i == a else a if i == b else i
            assert apply_word(vector, word) == BASIS[j]
        result[pair] = word
    return result


def stabilizer_generators():
    exchanges = exchange_words()
    witnesses = {}
    for i in range(7):
        witnesses[f"X[{i},{i + 1}]"] = exchanges[i, i + 1]
    for i in range(1, 8):
        # Z_k and the exchange (0,i) disagree at exactly those two
        # coordinates.  Their commutator is therefore M[0] M[i].
        k = next(k for k in range(3) if i & (1 << k))
        pair = "HH01" if k < 2 else "HH12"
        z = (pair, f"X{k}", pair)
        exchange = exchanges[0, i]
        word = z + exchange + z + exchange
        for j, vector in enumerate(BASIS):
            expected = tuple(-x for x in vector) if j in (0, i) else vector
            assert apply_word(vector, word) == expected
        witnesses[f"M[0] M[{i}]"] = word
    return witnesses


def apply_stabilizer_word(vector, word):
    """Apply the fourteen-generator signed-permutation alphabet."""
    vector = list(vector)
    for kind, index in word:
        if kind == "X":
            vector[index], vector[index + 1] = vector[index + 1], vector[index]
        elif kind == "M":
            vector[0], vector[index] = -vector[0], -vector[index]
        else:
            raise ValueError(kind)
    return tuple(vector)


def stabilizer_normal_form(permutation, negative_outputs):
    """A deterministic word, again in left-to-right application order."""
    current = list(range(8))
    result = []
    for i, target in enumerate(permutation):
        if current[i] == target:
            continue
        a, b = sorted((current[i], target))
        result += [("X", j) for j in range(a, b)]
        result += [("X", j) for j in reversed(range(a, b - 1))]
        current = [b if x == a else a if x == b else x for x in current]
    assert current == permutation
    assert len(negative_outputs) % 2 == 0
    result += [("M", i) for i in negative_outputs if i != 0]
    for i, vector in enumerate(BASIS):
        expected = BASIS[permutation[i]]
        if permutation[i] in negative_outputs:
            expected = tuple(-x for x in expected)
        assert apply_stabilizer_word(vector, result) == expected
    return result


def factorization_table(representatives, transitions):
    """Verify rep(c) g = h(c,g) rep(next(c,g)) for all 1080 cells.

    Representatives here are the stored lists read in repository matrix
    order, hence inverse to their left-to-right frame action.  Every
    returned h word is explicitly stored in repository matrix order.
    """
    table = []
    for c, route in enumerate(representatives):
        row = []
        for g, target in zip(NAMES, transitions[c]):
            target_route = representatives[target]
            # h = inverse(frame_rep(c)) * g * frame_rep(target).
            application_word = target_route + (g,) + tuple(reversed(route))
            columns = [apply_word(v, application_word) for v in BASIS]
            permutation, negative_outputs = [], []
            for column in columns:
                support = [i for i, x in enumerate(column) if x]
                assert len(support) == 1
                i = support[0]
                assert abs(column[i]) == 4
                permutation.append(i)
                if column[i] < 0:
                    negative_outputs.append(i)
            assert sorted(permutation) == list(range(8))
            negative_outputs.sort()
            normal = stabilizer_normal_form(permutation, negative_outputs)
            for vector in BASIS:
                lhs = apply_word(vector, (g,) + tuple(reversed(route)))
                rhs = apply_stabilizer_word(
                    apply_word(vector, tuple(reversed(target_route))), normal)
                assert lhs == rhs
            row.append({
                "next": target,
                "permutation": permutation,
                "negative_outputs": negative_outputs,
                "stabilizer_word_matrix_order": [[kind, index] for kind, index in reversed(normal)],
            })
        table.append(row)
    return table


def certificate():
    vectors = invariant_vectors()
    assert len(vectors) == 240
    for name in NAMES:
        assert {gate(name, v) for v in vectors} == vectors
    frames, representatives, transitions = frame_orbit()
    witnesses = stabilizer_generators()
    factorizations = factorization_table(representatives, transitions)
    # Any frame stabilizer is a signed permutation.  Preservation of the
    # all-ones invariant vector forces an even number of negative signs.
    # The verified adjacent exchanges and seven sign pairs generate all
    # such signed permutations, proving equality of the stabilizer.
    stabilizer_order = 2 ** 7 * factorial(8)
    assert len(frames) == 135
    assert stabilizer_order == 5_160_960
    order = len(frames) * stabilizer_order
    assert order == 696_729_600
    return {
        "schema": "ccx-hh-three-qubit-frame-orbit-v1",
        "method": "Integer frame orbit and explicit even-signed-permutation stabilizer witnesses",
        "status": "Exact finite diagnostic; not a formal completeness theorem",
        "word_order": "Gates apply from left to right; reverse lists for repository matrix order",
        "generators": list(NAMES),
        "preserved_vector_count": len(vectors),
        "frame_count": len(frames),
        "stabilizer_order": stabilizer_order,
        "group_order": order,
        "stabilizer_chain_orbit_sizes": [135, 16, 14, 12, 10, 8, 6, 4],
        "stabilizer_generator_words": {k: list(v) for k, v in witnesses.items()},
        "frames": [[list(v) for v in frame] for frame in frames],
        "representative_words": [list(w) for w in representatives],
        "transitions": transitions,
        "factorization_representative_order": "Stored representative lists read in repository matrix order",
        "factorization_equation": "rep(c) * g = h(c,g) * rep(next(c,g))",
        "factorizations": factorizations,
    }


def serialize(result):
    """Keep each frame, transition, and factorization cell on one line."""
    compact = lambda value: json.dumps(value, separators=(",", ":"))
    fields = []
    for key, value in result.items():
        prefix = "  " + json.dumps(key) + ": "
        if key == "factorizations":
            rows = ["    [\n" + ",\n".join("      " + compact(cell) for cell in row)
                    + "\n    ]" for row in value]
            fields.append(prefix + "[\n" + ",\n".join(rows) + "\n  ]")
        elif isinstance(value, list) and value and isinstance(value[0], list):
            fields.append(prefix + "[\n" + ",\n".join("    " + compact(row) for row in value) + "\n  ]")
        elif isinstance(value, dict):
            rows = ["    " + json.dumps(k) + ": " + compact(v) for k, v in value.items()]
            fields.append(prefix + "{\n" + ",\n".join(rows) + "\n  }")
        else:
            fields.append(prefix + compact(value))
    return "{\n" + ",\n".join(fields) + "\n}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write the deterministic JSON certificate")
    args = parser.parse_args()
    result = certificate()
    path = Path(__file__).with_name("finite_cosets.json")
    if args.write:
        path.write_text(serialize(result), encoding="utf-8")
    elif path.exists():
        assert json.loads(path.read_text(encoding="utf-8")) == result, "Stored certificate is stale"
    print(f"PASS: {len(NAMES)} physical generators preserve 240 vectors.")
    print(f"PASS: closed orbit of {result['frame_count']} coordinate frames; all representatives verified.")
    print("PASS: 14 physical circuit words generate the full frame stabilizer.")
    print("PASS: all 1080 coset factorizations have exact signed-permutation normal forms.")
    print(f"Circuit group order = {result['frame_count']} * {result['stabilizer_order']} = {result['group_order']}.")
    print("No ambient or published exceptional-group presentation was used.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Materialize and verify the 105 compact base rules and 1080 circuit rules.

The base rules are seven commuting phase involutions, adjacent exchanges
with the existing S8 relations, and their explicit conjugation action.
All are translated to physical X/CX/CCX/HH words.  This exact check is a
readable companion to the Agda translation, not a replacement for it.
"""

from itertools import combinations
from pathlib import Path
import argparse
import json
import finite_cosets as F

HERE = Path(__file__).resolve().parent


def base_relations():
    result = []

    def add(name, left, right):
        result.append({"name": name, "left": left, "right": right})

    for i in range(7):
        add(f"phase-square-{i}", [f"p{i}"] * 2, [])
    for i, j in combinations(range(7), 2):
        add(f"phase-commute-{i}-{j}", [f"p{i}", f"p{j}"], [f"p{j}", f"p{i}"])
    for i in range(7):
        add(f"exchange-square-{i}", [f"x{i}"] * 2, [])
    for i in range(6):
        add(f"braid-{i}", [f"x{i}", f"x{i+1}", f"x{i}"],
            [f"x{i+1}", f"x{i}", f"x{i+1}"])
    for i, j in combinations(range(7), 2):
        if j > i + 1:
            add(f"exchange-commute-{i}-{j}", [f"x{i}", f"x{j}"], [f"x{j}", f"x{i}"])
    for i in range(7):
        for j in range(7):
            if i == 0:
                action = ["p0"] if j == 0 else ["p0", f"p{j}"]
            elif j == i - 1:
                action = [f"p{i}"]
            elif j == i:
                action = [f"p{i-1}"]
            else:
                action = [f"p{j}"]
            add(f"cross-{i}-{j}", [f"x{i}", f"p{j}"], action + [f"x{i}"])
    assert len(result) == 105
    return result


def artifact(data):
    decoders = {}
    for i in range(7):
        decoders[f"x{i}"] = list(reversed(data["stabilizer_generator_words"][f"X[{i},{i+1}]"]))
        decoders[f"p{i}"] = list(reversed(data["stabilizer_generator_words"][f"M[0] M[{i+1}]"]))
    return {
        "method": "Clement translation from the repository Table 1, with a finite frame normal form",
        "word_order": "matrix multiplication order; apply physical lists from right to left",
        "letters": {"xi": "exchange levels i and i+1", "pi": "negate levels 0 and i+1"},
        "decoders_matrix_order": decoders,
        "base_relations": base_relations(),
        "coset_data": "finite_cosets.json",
        "coset_equation": "rep(c) g = decode(stabilizer_word_matrix_order) rep(next)",
        "relation_count": 1185,
    }


def decode(word, decoders):
    return [gate for letter in word for gate in decoders[letter]]


def assert_equal(name, left, right):
    assert all(F.apply_word(v, reversed(left)) == F.apply_word(v, reversed(right))
               for v in F.BASIS), f"Incorrect physical equation: {name}"


def verify(result, data):
    decoders = result["decoders_matrix_order"]
    for equation in result["base_relations"]:
        assert_equal(equation["name"], decode(equation["left"], decoders),
                     decode(equation["right"], decoders))
    count = 0
    for c, row in enumerate(data["factorizations"]):
        for gate, cell in zip(data["generators"], row):
            word = [f"x{i}" if kind == "X" else f"p{i-1}"
                    for kind, i in cell["stabilizer_word_matrix_order"]]
            left = data["representative_words"][c] + [gate]
            right = decode(word, decoders) + data["representative_words"][cell["next"]]
            assert_equal(f"table-{c}-{gate}", left, right)
            count += 1
    assert count + len(result["base_relations"]) == result["relation_count"]


def serialize(result):
    compact = lambda x: json.dumps(x, separators=(",", ":"))
    lines = []
    for key, value in result.items():
        prefix = "  " + json.dumps(key) + ": "
        if key == "base_relations":
            lines.append(prefix + "[\n" + ",\n".join("    " + compact(x) for x in value) + "\n  ]")
        elif key == "decoders_matrix_order":
            lines.append(prefix + "{\n" + ",\n".join("    " + json.dumps(k) + ": " + compact(v)
                         for k, v in value.items()) + "\n  }")
        else:
            lines.append(prefix + compact(value))
    return "{\n" + ",\n".join(lines) + "\n}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the compact JSON artifact")
    args = parser.parse_args()
    data = json.loads((HERE / "finite_cosets.json").read_text(encoding="utf-8"))
    result = artifact(data)
    verify(result, data)
    path = HERE / "compact_relations.json"
    if args.write:
        path.write_text(serialize(result), encoding="utf-8")
    else:
        assert json.loads(path.read_text(encoding="utf-8")) == result, "Stored compact artifact is stale"
    print("PASS: all 105 decoded base equations and 1080 coset equations hold as physical circuits.")
    print("The 1185 equations are specified by compact_relations.json and finite_cosets.json.")


if __name__ == "__main__":
    main()

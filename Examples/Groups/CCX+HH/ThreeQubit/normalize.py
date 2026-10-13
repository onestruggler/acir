#!/usr/bin/env python3
"""Normalize three-wire X,CX,CCX,HH circuits using the checked coset table.

Input and output words use matrix-product order: the rightmost gate acts
first.  The normal form is an even signed permutation followed by one of
the 135 representatives in finite_cosets.json.  This is an executable
companion to NormalForm.agda, not a new presentation or a proof checker.

Examples:
  python3 -B normalize.py X0 HH01 CX10 HH12
  python3 -B normalize.py --json 'X0 HH01 CX10 HH12'
  python3 -B normalize.py --self-test
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import random
import sys


NAMES = ("X0", "X1", "X2", "CX10", "CX21", "CCX210", "HH01", "HH12")
INDEX = {name: index for index, name in enumerate(NAMES)}
IDENTITY = tuple(range(8))
HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class SignedPermutation:
    """Column i is sign[permutation[i]] times basis[permutation[i]]."""

    permutation: tuple[int, ...] = IDENTITY
    negative_outputs: frozenset[int] = frozenset()

    def compose(self, right: SignedPermutation) -> SignedPermutation:
        """Matrix multiplication self * right; right acts first."""
        return SignedPermutation(
            tuple(self.permutation[i] for i in right.permutation),
            self.negative_outputs ^ frozenset(
                self.permutation[i] for i in right.negative_outputs),
        )

    def word(self) -> tuple[tuple[str, int], ...]:
        """A deterministic matrix-order word over the fourteen base gates."""
        current = list(IDENTITY)
        application_order = []
        for i, target in enumerate(self.permutation):
            if current[i] == target:
                continue
            a, b = sorted((current[i], target))
            application_order.extend(("X", j) for j in range(a, b))
            application_order.extend(("X", j) for j in reversed(range(a, b - 1)))
            current = [b if x == a else a if x == b else x for x in current]
        phases = tuple(("M", i) for i in range(1, 8) if i in self.negative_outputs)
        return phases + tuple(reversed(application_order))


@dataclass(frozen=True)
class NormalForm:
    stabilizer: SignedPermutation
    coset: int


class Normalizer:
    def __init__(self, path: Path = HERE / "finite_cosets.json"):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("schema") != "ccx-hh-three-qubit-frame-orbit-v1":
            raise ValueError("Unsupported finite coset data schema")
        if tuple(data["generators"]) != NAMES or data["frame_count"] != 135:
            raise ValueError("Unexpected generator alphabet or frame count")
        self.representatives = tuple(tuple(w) for w in data["representative_words"])
        self.witnesses = {
            ("X", i): tuple(reversed(data["stabilizer_generator_words"][f"X[{i},{i + 1}]" ]))
            for i in range(7)
        }
        self.witnesses.update({
            ("M", i): tuple(reversed(data["stabilizer_generator_words"][f"M[0] M[{i}]" ]))
            for i in range(1, 8)
        })
        self.table = []
        if len(self.representatives) != 135 or len(data["factorizations"]) != 135:
            raise ValueError("Incomplete coset table")
        for row in data["factorizations"]:
            if len(row) != len(NAMES):
                raise ValueError("Incomplete coset-table row")
            cells = []
            for cell in row:
                p = tuple(cell["permutation"])
                minus = frozenset(cell["negative_outputs"])
                target = cell["next"]
                if (sorted(p) != list(IDENTITY) or not minus <= set(IDENTITY)
                        or len(minus) % 2 or not 0 <= target < 135):
                    raise ValueError("Invalid signed-permutation table cell")
                cells.append((SignedPermutation(p, minus), target))
            self.table.append(tuple(cells))
        for word in (*self.representatives, *self.witnesses.values()):
            self.validate(word)

    @staticmethod
    def validate(word: tuple[str, ...]) -> None:
        for name in word:
            if name not in INDEX:
                raise ValueError(f"Unknown gate {name!r}; choose from {', '.join(NAMES)}")

    def normalize(self, word: tuple[str, ...]) -> NormalForm:
        self.validate(word)
        base, coset = SignedPermutation(), 0
        for name in word:
            factor, coset = self.table[coset][INDEX[name]]
            base = base.compose(factor)
        return NormalForm(base, coset)

    def circuit(self, normal: NormalForm) -> tuple[str, ...]:
        return tuple(g for atom in normal.stabilizer.word() for g in self.witnesses[atom]) \
            + self.representatives[normal.coset]

    def describe(self, normal: NormalForm) -> dict:
        base = normal.stabilizer
        return {
            "word_order": "matrix product order; rightmost gate acts first",
            "permutation": list(base.permutation),
            "permutation_convention": "input basis index -> output basis index",
            "signs": [-1 if i in base.negative_outputs else 1 for i in range(8)],
            "negative_outputs": sorted(base.negative_outputs),
            "coset": normal.coset,
            "stabilizer_word": [list(atom) for atom in base.word()],
            "representative_word": list(self.representatives[normal.coset]),
            "canonical_word": list(self.circuit(normal)),
        }


def self_test(normalizer: Normalizer) -> dict:
    """Check every cell and randomized normalization with independent matrices."""
    sys.path.insert(0, str(HERE.parent / "scripts"))
    from exact_matrices import append_gate, identity

    gates = {
        "X0": ("X", (0,)), "X1": ("X", (1,)), "X2": ("X", (2,)),
        "CX10": ("CX", (1, 0)), "CX21": ("CX", (2, 1)),
        "CCX210": ("CCX", (2, 1, 0)),
        "HH01": ("HH", (0, 1)), "HH12": ("HH", (1, 2)),
    }

    def matrix(word):
        value = identity(3)
        for name in word:
            value = append_gate(value, gates[name], 3)
        return value

    checked = 0

    def check(word):
        nonlocal checked
        normal = normalizer.normalize(word)
        canonical = normalizer.circuit(normal)
        assert matrix(word) == matrix(canonical), (word, normal)
        assert normalizer.normalize(canonical) == normal, (word, "section")
        checked += 1

    check(())
    for name in NAMES:
        check((name,))
        assert normalizer.normalize((name, name)) == NormalForm(SignedPermutation(), 0)
    for c, representative in enumerate(normalizer.representatives):
        assert normalizer.normalize(representative) == NormalForm(SignedPermutation(), c)
        for name in NAMES:
            check(representative + (name,))
    rng = random.Random(20261014)
    for length in (2, 3, 8, 20, 50, 100, 250):
        for _ in range(12):
            word = tuple(rng.choice(NAMES) for _ in range(length))
            check(word)
            at = rng.randrange(length + 1)
            name = rng.choice(NAMES)
            assert normalizer.normalize(word[:at] + (name, name) + word[at:]) == normalizer.normalize(word)
    # The generated normal form also accepts every abstract even signed
    # permutation, independently of which table words appeared above.
    for _ in range(64):
        permutation = list(IDENTITY)
        rng.shuffle(permutation)
        negative = {i for i in range(1, 8) if rng.randrange(2)}
        if len(negative) % 2:
            negative.add(0)
        normal = NormalForm(SignedPermutation(tuple(permutation), frozenset(negative)), rng.randrange(135))
        assert normalizer.normalize(normalizer.circuit(normal)) == normal
    return {"matrix_checks": checked, "table_cells": 1080,
            "random_words": 84, "abstract_section_checks": 64, "seed": 20261014}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("word", nargs="*", help="Matrix-order gate names, separately or as a quoted word")
    parser.add_argument("--json", action="store_true", help="Print structured normal form and canonical circuit")
    parser.add_argument("--self-test", action="store_true", help="Run exact deterministic validation")
    args = parser.parse_args()
    try:
        normalizer = Normalizer()
        if args.self_test:
            result = self_test(normalizer)
            print(json.dumps({"status": "PASS", **result}) if args.json else f"PASS: {result}")
        if args.word or not args.self_test:
            word = tuple(name for part in args.word for name in part.split())
            result = normalizer.describe(normalizer.normalize(word))
            if args.json:
                print(json.dumps(result, indent=2))
            else:
                print("Permutation (input -> output):", result["permutation"])
                print("Output signs:", result["signs"])
                print("Coset:", result["coset"])
                print("Canonical matrix-order word:", " ".join(result["canonical_word"]) or "identity")
    except (ValueError, OSError, KeyError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()

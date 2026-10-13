#!/usr/bin/env python3
"""Compare HH or H circuits by exact matrices, including their global sign.

Words use matrix-product order: the rightmost gate acts first.  Wire 0
is the least significant bit; CX and CCX list controls before target.
No normal form or physical decoding is computed.  This executable does
not emit an Agda derivation; Decision.agda supplies the certified decider.

  python compare_circuits.py --wires 4 --gate-set HH --left "HH:0,1 HH:0,1" --right ""
  python compare_circuits.py --wires 1 --gate-set H --left "X:0 H:0" --right "H:0 X:0" --json

Exit status is 0 for equality, 1 for inequality, and 2 for invalid input.
The implementation stores dense 2^n by 2^n matrices.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import random
import sys


_path = Path(__file__).resolve().parent / "GeneralN" / "normalize.py"
_spec = importlib.util.spec_from_file_location("ccx_comparison_arithmetic", _path)
arithmetic = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = arithmetic
_spec.loader.exec_module(arithmetic)


def _coefficient(numerator: int, exponent: int, denominator: int) -> tuple[int, int]:
    """Represent one entry as (a + b sqrt(2)) / 2^denominator."""
    odd = exponent % 2
    shifted = numerator << (denominator - (exponent + 1) // 2)
    return (0, shifted) if odd else (shifted, 0)


def compare(wires: int, gate_set: str, left: str, right: str) -> dict:
    if wires < 0:
        raise ValueError("wire count must be nonnegative")
    if gate_set not in ("HH", "H"):
        raise ValueError("gate set must be HH or H")
    left_word = arithmetic.parse_word([left], wires, gate_set)
    right_word = arithmetic.parse_word([right], wires, gate_set)
    a = arithmetic.physical_matrix(wires, left_word)
    b = arithmetic.physical_matrix(wires, right_word)
    result = {
        "format": "ccx-exact-circuit-comparison-v1",
        "wires": wires,
        "gate_set": ["X", "CX", "CCX", gate_set],
        "word_order": "matrix product order; rightmost gate acts first",
        "wire_order": "least significant bit first; controls before target",
        "left_gates": len(left_word),
        "right_gates": len(right_word),
        "equal": a == b,
        "comparison": "exact integer arithmetic, including global sign",
        "agda_derivation_emitted": False,
    }
    if a == b:
        return result
    common = max((a.exponent + 1) // 2, (b.exponent + 1) // 2)
    for i, (x, y) in enumerate(zip(a.entries, b.entries)):
        ax, ay = _coefficient(x, a.exponent, common), _coefficient(y, b.exponent, common)
        if ax != ay:
            row, column = divmod(i, 1 << wires)
            result["witness"] = {
                "row": row,
                "column": column,
                "basis_indices": "zero-based computational basis levels",
                "left": {"numerator": x, "sqrt2_denominator_exponent": a.exponent},
                "right": {"numerator": y, "sqrt2_denominator_exponent": b.exponent},
                "common_scale": {
                    "reading": "(rational_coefficient + radical_coefficient * sqrt(2)) / 2^denominator_exponent",
                    "denominator_exponent": common,
                    "left_coefficients": list(ax),
                    "right_coefficients": list(ay),
                    "difference_coefficients": [ax[0] - ay[0], ax[1] - ay[1]],
                },
            }
            return result
    raise AssertionError("different canonical matrices have identical exact entries")


def self_test() -> None:
    rng, cases = random.Random(20261014), 0
    # Equality testing must remain independent of normal-form synthesis.
    def forbidden(*args, **kwargs):
        raise AssertionError("comparison invoked normalization or circuit decoding")

    original = arithmetic.normalize_matrix, arithmetic.reduce_dyadic, arithmetic.decode_dyadic
    arithmetic.normalize_matrix = arithmetic.reduce_dyadic = arithmetic.decode_dyadic = forbidden
    try:
        for wires in range(7):
            for gate_set in ("HH", "H"):
                alphabet = tuple(arithmetic.gate_alphabet(wires, gate_set))
                samples = [(), *[(g,) for g in alphabet]]
                if alphabet:
                    samples += [tuple(rng.choice(alphabet) for _ in range(k)) for k in (3, 8, 17, 32)]
                for word in samples:
                    text = " ".join(map(arithmetic.format_gate, word))
                    reverse = " ".join(map(arithmetic.format_gate, reversed(word)))
                    value = arithmetic.dyadic.matrix(wires, word)
                    inverse = arithmetic.dyadic.matrix(wires, tuple(reversed(word)))
                    if arithmetic.physical_matrix(wires, word) != value:
                        raise AssertionError("batched arithmetic differs from literal gate evaluation")
                    result = compare(wires, gate_set, text, reverse)
                    if result["equal"] != (value == inverse):
                        raise AssertionError("comparison differs from independent exact matrices")
                    if not result["equal"]:
                        witness = result["witness"]
                        index = witness["row"] * (1 << wires) + witness["column"]
                        if witness["left"]["numerator"] != value.entries[index]:
                            raise AssertionError("wrong left witness entry")
                        if witness["right"]["numerator"] != inverse.entries[index]:
                            raise AssertionError("wrong right witness entry")
                        if witness["common_scale"]["difference_coefficients"] == [0, 0]:
                            raise AssertionError("zero inequality witness")
                    if not compare(wires, gate_set, text + " " + reverse, "")["equal"]:
                        raise AssertionError("word times its inverse is not identity")
                    cases += 1
        minus_one = " ".join(["X:0 H:0"] * 4)
        sign = compare(1, "H", minus_one, "")
        if sign["equal"] or sign["witness"]["common_scale"]["difference_coefficients"] != [-2, 0]:
            raise AssertionError("a nontrivial global sign was discarded")
        radical = compare(1, "H", "H:0", "")
        if radical["witness"]["common_scale"]["difference_coefficients"] != [-2, 1]:
            raise AssertionError("different sqrt(2) denominator parities were compared incorrectly")
        for wires, gate_set, left in ((-1, "HH", ""), (0, "H", "H:0"),
                                      (2, "HH", "CX:0,0"), (2, "HH", "H:0")):
            try:
                compare(wires, gate_set, left, "")
            except ValueError:
                pass
            else:
                raise AssertionError("invalid input was accepted")
    finally:
        arithmetic.normalize_matrix, arithmetic.reduce_dyadic, arithmetic.decode_dyadic = original
    print(f"PASS {cases} comparisons on 0 through 6 wires; independent matrices, inverse words, exact witnesses, global sign, radical scales and invalid inputs; no normalization calls.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--wires", type=int, default=4)
    parser.add_argument("--gate-set", choices=("HH", "H"), default="HH")
    parser.add_argument("--left", default="", help="left circuit as a quoted gate word")
    parser.add_argument("--right", default="", help="right circuit as a quoted gate word")
    parser.add_argument("--json", action="store_true", help="include exact witness details in JSON")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    try:
        result = compare(args.wires, args.gate_set, args.left, args.right)
    except ValueError as exc:
        parser.error(str(exc))
    if args.json:
        print(json.dumps(result, indent=2))
    elif result["equal"]:
        print(f"Equal: exact {args.gate_set} circuit matrices on {args.wires} wires, including global sign.")
    else:
        w = result["witness"]
        left, right = w["left"], w["right"]
        print(f"Unequal at row {w['row']}, column {w['column']}: "
              f"{left['numerator']}/sqrt(2)^{left['sqrt2_denominator_exponent']} != "
              f"{right['numerator']}/sqrt(2)^{right['sqrt2_denominator_exponent']}.")
    return 0 if result["equal"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

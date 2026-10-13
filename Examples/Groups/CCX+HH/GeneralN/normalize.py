#!/usr/bin/env python3
"""Exact circuit normalization on four or more wires, by Clément decoding.

Words use matrix-product order (the rightmost gate acts first).  Wire 0
is the least significant basis bit.  CX/CCX list controls before target.
Examples:
  python normalize.py --wires 4 --gate-set HH X:0 HH:0,1 CX:1,0
  python normalize.py --wires 4 --gate-set H H:0 CCX:2,1,0 --source-only --json

The deterministic source reduction is Algorithm 1's sign/exchange/K
column reduction.  The existing four-state Clément decoder translates
its charge-zero word into physical gates, without adding wires.  The
output is canonical for this executable algorithm, not asserted to be
the literal output of Agda's normalizer or a shortest circuit.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
import importlib.util
import json
from pathlib import Path
import random
import sys


_path = Path(__file__).resolve().parents[2] / "CCX+H" / "GeneralN" / "construct.py"
_spec = importlib.util.spec_from_file_location("ccx_normalizer_decoder", _path)
decoder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(decoder)
dyadic = decoder.dyadic
from exact_matrices import alphabet as gate_alphabet
Matrix, canonical = dyadic.Matrix, dyadic.canonical
Gate = tuple[str, tuple[int, ...]]
Word = tuple[Gate, ...]


def format_gate(gate: Gate) -> str:
    name, wires = gate
    return name + ":" + ",".join(map(str, wires))


def parse_word(tokens: list[str], wires: int, gate_set: str) -> Word:
    """Validate gates and accept either individual or quoted word tokens."""
    result = []
    arities = {"X": 1, "CX": 2, "CCX": 3, gate_set: 2 if gate_set == "HH" else 1}
    for token in " ".join(tokens).split():
        name, colon, raw = token.partition(":")
        if not colon or name not in arities:
            raise ValueError(f"invalid gate {token!r}; expected X, CX, CCX or {gate_set}")
        try:
            positions = tuple(int(x) for x in raw.split(","))
        except ValueError as exc:
            raise ValueError(f"invalid wire indices in {token!r}") from exc
        if len(positions) != arities[name] or len(set(positions)) != len(positions):
            raise ValueError(f"{token!r} needs {arities[name]} distinct wires")
        if any(x < 0 or x >= wires for x in positions):
            raise ValueError(f"wire outside 0..{wires - 1} in {token!r}")
        if name == "CCX":
            positions = tuple(sorted(positions[:-1])) + positions[-1:]
        elif name == "HH":
            positions = tuple(sorted(positions))
        result.append((name, positions))
    return tuple(result)


@lru_cache(maxsize=None)
def _classical_permutation(wires: int, gate: Gate) -> tuple[int, ...]:
    name, positions = gate
    if name not in ("X", "CX", "CCX"):
        raise ValueError(name)
    controls, target = positions[:-1], positions[-1]
    return tuple(i ^ (1 << target) if all(i & (1 << c) for c in controls) else i
                 for i in range(1 << wires))


@lru_cache(maxsize=None)
def _hadamard_pairs(wires: int, target: int) -> tuple[tuple[int, int], ...]:
    size, mask = 1 << wires, 1 << target
    return tuple((r * size + c, r * size + (c | mask))
                 for r in range(size) for c in range(size) if not c & mask)


@lru_cache(maxsize=4)
def physical_matrix(wires: int, word: Word) -> Matrix:
    """Exact gate matrices; batch consecutive classical column permutations.

    Hadamards use direct sum/difference tensor rows; the self-test checks
    these against exact_matrices.py's separate literal evaluator.  No
    source words or Schreier table are used to evaluate the output.
    """
    size = 1 << wires
    value = dyadic.identity(wires)
    identity = tuple(range(size))
    permutation = identity

    def flush(matrix: Matrix, perm: tuple[int, ...]) -> Matrix:
        if perm == identity:
            return matrix
        return Matrix(matrix.exponent, tuple(matrix.entries[r * size + perm[c]]
                                            for r in range(size) for c in range(size)))

    for gate in word:
        if gate[0] in ("X", "CX", "CCX"):
            following = _classical_permutation(wires, gate)
            permutation = tuple(permutation[i] for i in following)
        else:
            entries = flush(value, permutation).entries
            for target in gate[1]:
                out = list(entries)
                for p, q in _hadamard_pairs(wires, target):
                    out[p], out[q] = entries[p] + entries[q], entries[p] - entries[q]
                entries = tuple(out)
            value = canonical(value.exponent + len(gate[1]), entries)
            permutation = identity
    return flush(value, permutation)


def _validate_matrix(wires: int, value: Matrix) -> Matrix:
    size = 1 << wires
    if value.exponent < 0 or len(value.entries) != size * size:
        raise ValueError("matrix has the wrong dimension or a negative denominator exponent")
    if not all(isinstance(x, int) for x in value.entries):
        raise ValueError("matrix numerators must be integers")
    value = canonical(value.exponent, tuple(value.entries))
    for r in range(size):
        for s in range(r, size):
            inner = sum(value.entries[r * size + c] * value.entries[s * size + c]
                        for c in range(size))
            if inner != (1 << value.exponent if r == s else 0):
                raise ValueError("matrix is not orthogonal")
    return value


def reduce_dyadic(wires: int, value: Matrix) -> Word:
    """Return a deterministic Table 1 word with exactly the given matrix.

    Fix columns from last to first.  At a positive least denominator
    exponent, odd numerators occur in groups of four.  Negate the ones
    congruent to 3 mod 4, then use K to make the selected four even.
    Earlier row operations never disturb already fixed later columns.
    """
    if value.exponent % 2:
        raise ValueError("dyadic reduction requires an even sqrt(2) exponent")
    size = 1 << wires
    current, operations = value, []

    def apply(letter: Gate) -> None:
        nonlocal current
        name, indices = letter
        rows = [list(current.entries[r * size:(r + 1) * size]) for r in range(size)]
        exponent = current.exponent
        if name == "M":
            a, = indices
            rows[a] = [-x for x in rows[a]]
        elif name == "X":
            a, b = indices
            rows[a], rows[b] = rows[b], rows[a]
        elif name == "K":
            old = [rows[i] for i in indices]
            rows = [[2 * x for x in row] for row in rows]
            for r, a in enumerate(indices):
                rows[a] = [sum((-1 if (r & j).bit_count() % 2 else 1) * old[j][c]
                               for j in range(4)) for c in range(size)]
            exponent += 2
        else:
            raise ValueError(name)
        current = canonical(exponent, tuple(x for row in rows for x in row))
        operations.append(letter)

    for column in reversed(range(size)):
        while True:
            denominator = current.exponent // 2
            numerators = [current.entries[r * size + column] for r in range(column + 1)]
            if not any(numerators):
                raise ValueError("zero pivot column during orthogonal reduction")
            while denominator and all(x % 2 == 0 for x in numerators):
                denominator -= 1
                numerators = [x // 2 for x in numerators]
            if not denominator:
                occupied = [i for i, x in enumerate(numerators) if x]
                if len(occupied) != 1 or abs(numerators[occupied[0]]) != 1:
                    raise ValueError("non-unit integral pivot column")
                pivot = occupied[0]
                if pivot != column:
                    apply(("X", (pivot, column)))
                if numerators[pivot] == -1:
                    apply(("M", (column,)))
                break
            odd = [i for i, x in enumerate(numerators) if x % 2]
            if len(odd) % 4:
                raise ValueError("odd pivot support is not a multiple of four")
            block = tuple(odd[:4])
            for row in block:
                if numerators[row] % 4 == 3:
                    apply(("M", (row,)))
            apply(("K", block))
    if current != dyadic.identity(wires):
        raise AssertionError("source reduction did not reach the identity")
    # The chronological left operations are involutions.  Their written
    # matrix product equals the original matrix (not its inverse).
    return tuple(operations)


def decode_dyadic(wires: int, source: Word) -> Word:
    state, pieces = (0, 0), []
    for letter in source:
        name, indices = letter
        if name in ("M", "X"):
            pieces.append(decoder.signed_permutation(wires, decoder.edge_word(state, letter)))
        elif name == "K":
            t, s = decoder.k_factors(wires, state, indices)
            ts, ss = decoder.signed_permutation(wires, t), decoder.signed_permutation(wires, s)
            pieces.append(ts + dyadic.inverse(ss) + dyadic.mixed(wires, indices) + ss)
        else:
            raise ValueError(name)
        state = decoder.step(state, letter)
    if state != (0, 0):
        raise ValueError(f"matrix has dyadic charge {state}, outside the HH circuit image")
    return tuple(g for piece in pieces for g in piece)


def cancel_involutions(word: Word) -> Word:
    result = []
    for gate in word:
        if result and result[-1] == gate:
            result.pop()
        else:
            result.append(gate)
    return tuple(result)


def cancel_disjoint_involutions(word: Word) -> Word:
    """Cancel equal gates across gates on disjoint wires, in linear time.

    A previous gate can cancel exactly when it is the most recent gate
    on every one of its wires.  Deleted gates restore those wire links;
    intervening gates are disjoint and keep their original order.
    """
    nodes, previous, latest = [], [], {}
    for gate in word:
        links = tuple(latest.get(wire) for wire in gate[1])
        candidate = links[0]
        if candidate is not None and all(i == candidate for i in links) and nodes[candidate] == gate:
            nodes[candidate] = None
            for wire, link in zip(gate[1], previous[candidate]):
                latest[wire] = link
        else:
            for wire in gate[1]:
                latest[wire] = len(nodes)
            nodes.append(gate)
            previous.append(links)
    return tuple(gate for gate in nodes if gate is not None)


@dataclass(frozen=True)
class SourceNormalForm:
    source: Word
    parity: int

    def as_json(self, wires: int, gate_set: str, input_length: int) -> dict:
        return {
            "format": "ccx-clement-source-normal-form-v1",
            "wires": wires,
            "gate_set": ["X", "CX", "CCX", gate_set],
            "word_order": "matrix product order; rightmost gate acts first",
            "wire_order": "least significant bit first; controls before target",
            "input_gates": input_length,
            "hadamard_parity": self.parity,
            "source_word": [format_gate(g) for g in self.source],
            "source_indices": "computational basis levels, not wire numbers",
            "source_length": len(self.source),
            "verified_exact_matrix": True,
            "source_reading": "matrix(source_word) times H on wire 0 to the hadamard_parity power",
            "normal_form_convention": "deterministic executable choices; not asserted identical to Agda's word",
        }


@dataclass(frozen=True)
class NormalForm(SourceNormalForm):
    circuit: Word
    simplified: bool = False

    def as_json(self, wires: int, gate_set: str, input_length: int) -> dict:
        data = super().as_json(wires, gate_set, input_length)
        data.update({
            "format": "ccx-clement-normal-form-v1",
            "canonical_word": [format_gate(g) for g in self.circuit],
            "canonical_length": len(self.circuit),
            "disjoint_gate_cancellation": self.simplified,
        })
        return data


def _source_normalize(wires: int, gate_set: str, value: Matrix) -> tuple[SourceNormalForm, Matrix]:
    if wires < 4 or gate_set not in ("HH", "H"):
        raise ValueError("this normalizer supports HH or H on at least four wires")
    value = _validate_matrix(wires, value)
    parity = value.exponent % 2
    if gate_set == "HH" and parity:
        raise ValueError("an odd denominator parity is outside the HH image")
    body = dyadic.append_gate(value, ("H", (0,)), wires) if parity else value
    source = reduce_dyadic(wires, body)
    if decoder.source_matrix(wires, source) != body:
        raise AssertionError("source reconstruction failed")
    state = (0, 0)
    for letter in source:
        state = decoder.step(state, letter)
    if state != (0, 0):
        raise ValueError(f"matrix has dyadic charge {state}, outside the circuit image")
    reconstructed = dyadic.append_gate(body, ("H", (0,)), wires) if parity else body
    if reconstructed != value:
        raise AssertionError("source and parity do not reconstruct the input matrix")
    return SourceNormalForm(source, parity), value


def source_normalize_matrix(wires: int, gate_set: str, value: Matrix) -> SourceNormalForm:
    """Canonical exact source word and parity, without expanding physical gates."""
    return _source_normalize(wires, gate_set, value)[0]


def normalize_matrix(wires: int, gate_set: str, value: Matrix, simplify: bool = False) -> NormalForm:
    normal, value = _source_normalize(wires, gate_set, value)
    source, parity = normal.source, normal.parity
    cancel = cancel_disjoint_involutions if simplify else cancel_involutions
    circuit = cancel(dyadic.to_adjacent(wires, cancel(decode_dyadic(wires, source))))
    if gate_set == "H":
        circuit = cancel(decoder.expand_hh(circuit) + (("H", (0,)),) * parity)
    if physical_matrix(wires, circuit) != value:
        raise AssertionError("decoded circuit does not have the original exact matrix")
    return NormalForm(source, parity, circuit, simplify)


def normalize(wires: int, gate_set: str, word: Word, simplify: bool = False) -> NormalForm:
    return normalize_matrix(wires, gate_set, physical_matrix(wires, word), simplify)


def self_test_source() -> None:
    """Check compact normal forms without ever calling the circuit decoder."""
    global decode_dyadic
    original_decoder = decode_dyadic

    def forbidden(*args, **kwargs):
        raise AssertionError("source-only mode called the physical circuit decoder")

    decode_dyadic = forbidden
    rng, cases = random.Random(20261014), 0
    try:
        for wires in (4, 5, 6):
            for gate_set in ("HH", "H"):
                alphabet = tuple(gate_alphabet(wires, gate_set))
                for length in (0, 1, 3, 8, 12):
                    word = tuple(rng.choice(alphabet) for _ in range(length))
                    value = physical_matrix(wires, word)
                    normal = source_normalize_matrix(wires, gate_set, value)
                    source_value = decoder.source_matrix(wires, normal.source)
                    rebuilt = dyadic.append_gate(source_value, ("H", (0,)), wires) if normal.parity else source_value
                    if rebuilt != value or source_normalize_matrix(wires, gate_set, rebuilt) != normal:
                        raise AssertionError("source-only reconstruction or idempotence failed")
                    g = rng.choice(alphabet)
                    if source_normalize_matrix(wires, gate_set, physical_matrix(wires, (g, g) + word)) != normal:
                        raise AssertionError("equivalent inputs have different source normal forms")
                    if normal.parity != sum(kind == "H" for kind, _ in word) % 2:
                        raise AssertionError("source-only parity changed")
                    if "canonical_word" in normal.as_json(wires, gate_set, length):
                        raise AssertionError("source-only output claims to contain physical gates")
                    cases += 1
        for letter in (("M", (0,)), ("X", (0, 1)), ("K", (0, 1, 2, 3))):
            try:
                source_normalize_matrix(4, "HH", dyadic.expected(4, *letter))
            except ValueError:
                pass
            else:
                raise AssertionError("source-only mode accepted a matrix outside the physical image")
    finally:
        decode_dyadic = original_decoder
    print(f"PASS {cases} source-only normalizations on 4/5/6 wires; reconstruction, idempotence, equivalence, parity and 3 subgroup exclusions; no physical decoder calls.")


def self_test(simplify: bool = False) -> None:
    rng = random.Random(20261014)
    cases, rejected = 0, 0
    for wires in (4, 5):
        for gate_set in ("HH", "H"):
            alphabet = tuple(gate_alphabet(wires, gate_set))
            samples = [(), ((gate_set, (0, 1) if gate_set == "HH" else (0,)),),
                       (("CCX", (1, 2, 0)),),
                       ((gate_set, (0, 1) if gate_set == "HH" else (0,)),
                        ("CCX", (1, 2, 0)),
                        (gate_set, (1, 2) if gate_set == "HH" else (2,)))]
            samples += [tuple(rng.choice(alphabet) for _ in range(length)) for length in (3, 5, 8, 12)]
            for word in samples:
                value = physical_matrix(wires, word)
                if value != dyadic.matrix(wires, word):
                    raise AssertionError("batched physical evaluator disagrees with literal gate multiplication")
                if physical_matrix(wires, cancel_disjoint_involutions(word)) != value:
                    raise AssertionError("disjoint-gate cancellation changed the matrix")
                normal = normalize_matrix(wires, gate_set, value, simplify)
                if normal.parity != sum(kind == "H" for kind, _ in word) % 2:
                    raise AssertionError("Hadamard parity changed")
                if parse_word([format_gate(g) for g in normal.circuit], wires, gate_set) != normal.circuit:
                    raise AssertionError("output gate tokens do not round-trip")
                again = normalize(wires, gate_set, normal.circuit, simplify)
                if again != normal:
                    raise AssertionError("normalization is not literally idempotent")
                g = rng.choice(alphabet)
                equivalent = normalize(wires, gate_set, (g, g) + word, simplify)
                if equivalent != normal:
                    raise AssertionError("equivalent inputs produced different canonical words")
                allowed = {"X", "CX", "CCX", gate_set}
                for kind, positions in normal.circuit:
                    if kind not in allowed:
                        raise AssertionError("output contains a gate outside the selected alphabet")
                    if kind in ("CX", "CCX") and positions != tuple(range(positions[-1] + 1, positions[-1] + len(positions))) + positions[-1:]:
                        raise AssertionError("output contains a nonadjacent controlled gate")
                    if kind == "HH" and positions[1] != positions[0] + 1:
                        raise AssertionError("output contains a nonadjacent HH gate")
                cases += 1
                print(f"PASS {gate_set} n={wires} input={len(word)} source={len(normal.source)} output={len(normal.circuit)}", flush=True)
    for matrix in (dyadic.expected(4, "M", (0,)), dyadic.expected(4, "X", (0, 1)),
                   dyadic.expected(4, "K", (0, 1, 2, 3))):
        try:
            normalize_matrix(4, "HH", matrix)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("accepted an auxiliary generator outside the circuit subgroup")
    print(f"PASS {cases} normalizations, exact reconstruction, idempotence and equivalent inputs; {rejected} subgroup exclusions.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--wires", type=int, default=4)
    parser.add_argument("--gate-set", choices=("HH", "H"), default="HH")
    parser.add_argument("--json", action="store_true", help="print the full normal form as JSON")
    parser.add_argument("--output", type=Path, help="write the full JSON normal form to a file")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--source-only", action="store_true",
                        help="return the canonical auxiliary word and parity without expanding physical gates")
    parser.add_argument("--simplify", action="store_true",
                        help="also cancel equal gates across gates on disjoint wires")
    parser.add_argument("gates", nargs="*", help="gate tokens, e.g. X:0 CX:1,0 CCX:2,1,0 HH:0,1")
    args = parser.parse_args()
    if args.source_only and args.simplify:
        parser.error("--simplify applies to physical circuits and cannot be combined with --source-only")
    if args.self_test:
        self_test_source() if args.source_only else self_test(args.simplify)
        return
    try:
        if args.wires < 4:
            raise ValueError("use at least four wires (HH3 has a separate normalizer)")
        word = parse_word(args.gates, args.wires, args.gate_set)
        result = (source_normalize_matrix(args.wires, args.gate_set, physical_matrix(args.wires, word))
                  if args.source_only else normalize(args.wires, args.gate_set, word, args.simplify))
    except ValueError as exc:
        parser.error(str(exc))
    data = result.as_json(args.wires, args.gate_set, len(word))
    payload = json.dumps(data, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
    if args.json:
        print(payload, end="")
    else:
        detail = "physical expansion omitted" if args.source_only else f"{len(result.circuit)} canonical gates"
        print(f"Verified {args.gate_set} on {args.wires} wires: {len(word)} input gates; "
              f"{len(result.source)} auxiliary letters; {detail}; parity {result.parity}.")
        if args.output:
            print(f"Normal form written to {args.output}")
        else:
            output_word = result.source if args.source_only else result.circuit
            print(" ".join(format_gate(g) for g in output_word) or "identity")
            if args.source_only:
                print("Auxiliary indices are basis levels; append H:0 when parity is 1.")


if __name__ == "__main__":
    main()

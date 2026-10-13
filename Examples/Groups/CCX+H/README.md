# X, CX, CCX and H: Clément translation experiment

This development uses the scaled presentation in
[`CCX+HH-TwoLevel/Scaled`](../CCX+HH-TwoLevel/Scaled/) and Clément's
encode/decode argument from [`Real-Clifford+CH`](../Real-Clifford+CH/).
No relations or presentation method from arXiv:2407.11152 are imported.
The general-width completeness theorem is **still open**.

## Encoding

`Syntactics.agda` uses exactly `X`, `CX`, `CCX`, and `H` on
`Circuit.Base`. Wire 0 is the least significant basis bit, controlled
gates target their bottom wire, and words denote matrix products in
written order. Equality is exact, including global phase/sign.

`Encoding.agda` reuses the classical block encodings from `CCX+HH`.
An `H` on wire 0 is the single global auxiliary generator `IH`;
an `H` on another wire is a conjugate of `IH` by an explicit wire
permutation. This distinction matters: individual two-level Hadamards
are not generators of the scaled dyadic presentation.

## Concrete Clément translations

On one, two and three wires the auxiliary generators have explicit decodings
into circuits on the same wires. The resulting circuit relations are:

1. `D(u) = D(v)` for every instance `u = v` of the source Tables 1 and 2;
2. `g = D(E(g))` for each primitive circuit generator at that width.

These are finite presentations at each fixed width: the source indices
range over two, four or eight levels. They are not minimized lists of
local identities. The explicit circuit equations are available in
`one_qubit_relations.json` (11), `two_qubit_relations.json` (69), and
`three_qubit_relations.json` (2142). Their `left` and `right` lists refer to
the listed primitive circuit generators, with no auxiliary gates left.
There are respectively two, five and nine generator recovery equations.

`OneQubit.agda` directly decodes the two signs, exchange and global `IH`
on two levels. It uses the same translated-source/recovery construction.

`TwoQubit/Decoding.agda` realizes all 12 auxiliary generators on four
levels. Signs are conjugates of `CZ = H0 CX10 H0`, exchanges are short
classical circuits, `K` is `H0 H1`, and `IH` is `H0`.
`TwoQubit.agda` assembles the corresponding soundness/completeness proof.

`ThreeQubit/Decoding.agda` realizes all 107 auxiliary generators on eight
levels: eight signs, 28 exchanges, 70 four-level K gates, and `IH`.
The key construction is a local K on levels 0,1,2,3:

```
K0123 = M0 (H0 H1) M0 (H0 H1) M0 X[1,2].
```

Here `M0` is a sign on basis state 000, realized using an X-conjugate of
`H0 CCX H0`; `X[1,2]` is a two-level exchange realized by a conjugate of
CCX. Routing the four basis states gives the other K gates. These are
ordinary circuits with no ancillas. `build_decoding.py` checks all 107
images independently with exact arithmetic.

`ThreeQubit/DecodingSoundness.agda` verifies the section
`matrix(E(D(y))) = matrix(y)` in Agda. It factors long decodings through
short checked atoms so matrix computations need not be repeated.
`ThreeQubit/Presentation.agda` then obtains circuit completeness from the
existing scaled two-level theorem and the shared `CCX+HH/Translation`.
`ThreeQubit/Semantics.agda` provides independent gate-matrix semantics and
the bridge from the encoder.

The top-level soundness/completeness results use the direct matrix
semantics in `Semantics.agda`; their statements have no outstanding
decoding or semantic-correctness hypotheses at these fixed widths.

## Scope

The all-width compiler is defined, but a semantic bridge at arbitrary
width and the required larger-width subgroup presentation are not yet
proved. In particular, from four wires onward all requested circuit
generators have determinant +1, so the full scaled auxiliary alphabet
cannot have a same-width semantic decoder. Clément's subgroup step is
necessary before extending the construction.

`Certificates.agda` is only an auxiliary proof-certificate interface:
its relation wraps derivations between encodings, and its denotation is
defined through that encoding. It is not the circuit presentation or a
substitute for the decoding argument above. `Zero.agda` handles empty
circuits at width zero.

## Reproduction

With Agda 2.8.0, standard-library 2.4 and EucDomain registered, run from
the repository root:

```sh
agda Examples/Groups/CCX+H/OneQubit.agda
agda Examples/Groups/CCX+H/TwoQubit.agda
agda Examples/Groups/CCX+H/ThreeQubit/Presentation.agda
agda Examples/Groups/CCX+H/ThreeQubit/Semantics.agda
agda Examples/Groups/CCX+H/Zero.agda
agda Examples/Groups/CCX+H/Certificates.agda
python3 -B Examples/Groups/CCX+H/TwoQubit/build_checks.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_decoding.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_soundness.py
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 1 --check Examples/Groups/CCX+H/one_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 2 --check Examples/Groups/CCX+H/two_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 3 --check Examples/Groups/CCX+H/three_qubit_relations.json
```

The Python generators emit ordinary safe Agda definitions and proof
terms. Regeneration alone is not validation: rerun the Agda entry points
after generating them. No postulates or admitted holes are used.

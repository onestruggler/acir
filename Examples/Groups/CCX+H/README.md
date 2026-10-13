# X, CX, CCX and H: complete Clément translations

This development uses the scaled presentation in
[`CCX+HH-TwoLevel/Scaled`](../CCX+HH-TwoLevel/Scaled/) and Clément's
encode/decode argument from [`Real-Clifford+CH`](../Real-Clifford+CH/).
No relations or presentation method from arXiv:2407.11152 are imported.
The circuit theory is sound and complete at every width. The general
case is `GeneralN/CircuitPresentation.agda`, with no decoder or
semantic-correctness hypotheses; `Presentation.agda` combines it with
the existing zero-, one-, two-, and three-wire results.
`Orthogonal.agda` packages the same theorem as a group sub-presentation
of `O(2^n, ℤ[1/√2])` at every width.
`Structural.agda` derives addition of idle wires (`cong↑`, `cong⇓`,
`cong↑ᵏ`) and commutation with disjoint one-, two-, and three-wire gates
(`comm₁`, `comm₂`, `comm₃`) from this complete theory. These proofs use
independent tensor semantics and introduce no further circuit axioms.

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

The fixed-width soundness/completeness results use the direct matrix
semantics in `Semantics.agda`. The uniform `Presentation.agda` interface
uses `GeneralN/PhysicalSemantics.agda`: ordinary `2^n × 2^n` matrices
defined by independent Boolean and Hadamard tensor actions.
`GeneralN/SmallPhysicalSemantics.agda` identifies these with the direct
basis-entry matrices on one, two and three wires.

## The all-width construction

`GeneralN/Action.agda` and `GeneralN/Presentation.agda` now prove the
required four-state auxiliary subgroup presentation from Tables 1 and 2.
The dyadic letters act by charges `M -> 10`, `X -> 11`, `K -> 01`;
`IH` fixes states 00 and 01 and exchanges 10 with 11. A decoder for this
stabilizer is the correct general-width target.

`GeneralN/HadamardSchreier.agda` proves that each `IH` edge is `H0` or
`M0 M1 H0`. `DyadicSchreier.agda` formally reduces every K edge to even
signed permutations and a mixed `M_a X_bc K_abcd` block, using only
source relations. `GeneralN/construct.py` realizes all these edge types
as physical circuits, reusing the borrowed-bit constructions in `CCX+HH`.
At four wires the exact audit checks all 7,828 source plans and sampled
fully expanded circuits. `GeneralN/Decoding.md` gives the derivation.

`GeneralN/EdgePlans.agda` proves every dyadic edge factorization, including
coincident indices in the signed part. The physical constructions in
`CCX+HH/GeneralN` realize sign pairs, double exchanges, paired K blocks
and mixed atoms on the same wires. `GeneralN/HadamardEmbedding.agda`
expands each physical `HH` into two `H` gates and proves preservation
of the independently defined physical matrices at every positive width.
`GeneralN/DecoderLift.agda` combines this with the four `IH` reductions;
`GeneralN/Decoding.agda` supplies the unconditional decoder.

`CircuitTranslation.agda` carries out the two Clément translations:
first from the scaled source to its four-state stabilizer, then from
that auxiliary theory to actual circuits. Instantiating it in
`GeneralN/CircuitPresentation.agda` proves exact matrix soundness and
completeness at every width at least four. `GeneralN/Generation.agda`
also gives explicit synthesis for every source word fixing `00`, and
proves that this condition is necessary for physical realizability.

These are finite translated presentations at each fixed width. They
are not a short width-independent list of local circuit identities.
For `N=2^w`, let `g=N+C(N,2)+C(N,4)` and let `R` be the number of
Table 1 instances. The raw rule count is
`4(R + N + 2 + g + 1) + 4w - 3`: four-state translations and recovery
equations, followed by the physical gate recovery equations. It is
4,418,737 at four wires, before removing trivial or repeated equations.
See `CCX+HH/GeneralN/relation_counts.py` for the source counting formula.

`Certificates.agda` is only an auxiliary proof-certificate interface:
its relation wraps derivations between encodings, and its denotation is
defined through that encoding. It is not the circuit presentation or a
substitute for the decoding argument above. `Zero.agda` handles empty
circuits at width zero.

## Reproduction

With Agda 2.8.0, standard-library 2.4 and EucDomain registered, run from
the repository root:

```sh
agda Examples/Groups/CCX+H/Presentation.agda
agda Examples/Groups/CCX+H/Orthogonal.agda
agda Examples/Groups/CCX+H/Structural.agda
agda Examples/Groups/CCX+H/GeneralN/Generation.agda
agda Examples/Groups/CCX+H/OneQubit.agda
agda Examples/Groups/CCX+H/TwoQubit.agda
agda Examples/Groups/CCX+H/ThreeQubit/Presentation.agda
agda Examples/Groups/CCX+H/ThreeQubit/Semantics.agda
agda Examples/Groups/CCX+H/Zero.agda
agda Examples/Groups/CCX+H/Certificates.agda
agda Examples/Groups/CCX+H/GeneralN/Presentation.agda
agda Examples/Groups/CCX+H/GeneralN/DyadicSchreier.agda
agda Examples/Groups/CCX+H/GeneralN/HadamardSchreier.agda
python3 -B Examples/Groups/CCX+H/TwoQubit/build_checks.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_decoding.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_soundness.py
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 1 --check Examples/Groups/CCX+H/one_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 2 --check Examples/Groups/CCX+H/two_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 3 --check Examples/Groups/CCX+H/three_qubit_relations.json
python3 -B Examples/Groups/CCX+H/GeneralN/construct.py --wires 4 --samples 4
```

The Python generators emit ordinary safe Agda definitions and proof
terms. Regeneration alone is not validation: rerun the Agda entry points
after generating them. No postulates or admitted holes are used.

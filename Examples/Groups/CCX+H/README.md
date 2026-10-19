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

`Normalization.agda` gives a canonical circuit normalizer at every width.
Its output is an actual circuit: equal physical matrices produce literally
equal output words, normalization preserves the matrix, and applying it
twice gives the same word. On one through three wires it canonically
normalizes the scaled auxiliary word before decoding. At larger widths it
normalizes an HH component and appends the remaining H parity bit. This
construction is not claimed to minimize circuit length or run efficiently.
An executable companion for widths at least four is
[`CCX+HH/GeneralN/normalize.py`](../CCX+HH/GeneralN/normalize.py), used with
`--gate-set H`. Its `--source-only` option returns the exact canonical
auxiliary word and H parity without expanding a long physical circuit;
see the [normalization commands](../CCX+HH/GeneralN/README.md#executable-normalization).
`GeneralN/HadamardParity.agda` separately proves that matrix equality
preserves the number of H gates modulo two, at every width; expansions of
HH circuits always have even parity.

`Decision.agda` decides circuit equality at every width by exact matrix
comparison and returns either a derivation in the complete theory or a
proof of inequality. `DecisionExamples.agda` checks cancellation,
noncommutation, and retention of a nontrivial global sign through this
decision procedure.
For an executable exact comparison without normal-form expansion, use
[`CCX+HH/compare_circuits.py`](../CCX+HH/compare_circuits.py) with
`--gate-set H --wires N --left "..." --right "..."`. It keeps global
signs and reports a differing exact matrix entry when unequal; it does
not emit an Agda derivation.

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
`OneQubitReduced.agda` then derives an equivalent three-rule theory:
`X² = H² = (XH)⁸ = 1`. Its completeness follows by deriving all eleven
translated equations using the checked involutory relator reducer in
`CCX+HH/RelatorReduction.agda`.

`TwoQubit/Decoding.agda` realizes all 12 auxiliary generators on four
levels. Signs are conjugates of `CZ = H0 CX10 H0`, exchanges are short
classical circuits, `K` is `H0 H1`, and `IH` is `H0`.
`TwoQubit.agda` assembles the corresponding soundness/completeness proof.
`TwoQubit/ReducedPresentation.agda` proves an equivalent **42-equation**
theory: five gate involutions and 37 cyclic relators. The reduction uses
the same checked cancellation, conjugation, rotation, and reversal
certificates as the HH two-wire reduction. The explicit words and
certificates are in `two_qubit_reduced.json`; reproduce them with
`python3 -B Examples/Groups/CCX+H/scripts/build_reduced_relations.py --check`
and typecheck `Examples/Groups/CCX+H/TwoQubit/ReducedPresentation.agda`.
`TwoQubit/ShortPresentation.agda` reduces this further to **19 equations**
(five involutions and fourteen relators). Every shortening step is a
proved consequence of other current Clément relators, with proofs in both
directions. The explicit equations and rewrite certificates are in
`two_qubit_short.json`. Reproduce them with
`python3 -B Examples/Groups/CCX+HH/scripts/build_short_relations.py --gate-set H --check`
and typecheck `Examples/Groups/CCX+H/TwoQubit/ShortPresentation.agda`.

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
short checked atoms so matrix computations need not be repeated. Each
atom's identity is decided by one boolean (`by-eq√` of
`CCX+HH/Decide.agda`) rather than by `refl`, which would make Agda
compare the two matrices entry by entry.
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

`GeneralN/HadamardDecomposition.agda` strengthens this description at
widths at least four: every H circuit is an embedded HH circuit followed
by either identity or `H0`. Both components are unique, with the HH
component compared in its complete circuit theory. Consequently the HH
image is exactly the circuits with even H count. This statement is
specific to widths at least four; the smaller widths use their separate
complete presentations above.

`GeneralN/HadamardAction.agda` constructs the involutive automorphism
`α(u) = H0 u H0` of the HH group and proves its product and unit laws.
Together with the unique decomposition, its multiplication theorem
identifies the H group as `HH ⋊ C₂`, with
`(u,b)(v,c) = (u α^b(v), b xor c)`.
`GeneralN/SemidirectProduct.agda` packages this multiplication as
a standard `Group` and the realization map as an `IsGroupIsomorphism`.
The ambient scaled two-level group is larger:
`GeneralN/NonNormal.agda` proves that conjugating its realizable
`IH` by a single basis-state sign gives a nonrealizable matrix. Thus the
physical H image is not normal in that ambient group.

`GeneralN/DihedralQuotient.agda` identifies the complete eight-element
image of the ambient four-state action with the dihedral group `D₈`.
It supplies a group homomorphism, a faithful action, and representatives
of all eight values. `GeneralN/DihedralKernel.agda` proves that the HH
image is exactly its kernel at widths at least four, including synthesis
of every kernel element and of every ambient conjugate. Every ambient
word factors as an HH circuit times one of eight representatives, with
unique coset value. The H image is precisely the preimage of the
two-element reflection subgroup.

`GeneralN/ScaledAbelianization.agda` computes the ambient scaled
presentation's abelianization as `C₂ × C₂`, already with two levels.
The two characters are the first charge bit and H parity, with
representatives `1`, `M0`, `IH`, and `M0 IH`. It proves the universal
commutative quotient and a standard group isomorphism. Its derived
subgroup consists exactly of the two D₈ values `q00` and `q01`; this
differs from the physical H and HH derived-subgroup statements above.
`GeneralN/AmbientCosets.agda` gives its four cosets explicitly: every
ambient word is an H circuit times a representative indexed by the
four-state action, and equality of two such products forces the same
state. Thus H has index four, while HH has index eight.

`Abelianization.agda` defines the universal commutative quotient by
adding commutation of arbitrary words. At widths at least four,
`GeneralN/Abelianization.agda` proves that this quotient is exactly
`C₂`, with a standard group isomorphism given by H parity. It also
identifies the derived subgroup with the embedded HH group, including
an HH circuit witness for every member. These added commutations
describe the quotient; they are not physical circuit identities.
`LowWidthAbelianization.agda` transports the full scaled source result
through the verified decoders on one, two and three wires.
`AbelianizationClassification.agda` assembles standard group
isomorphisms at every width:

| Wires | Abelianization | Characters |
|---|---|---|
| 0 | Trivial | None |
| 1 | `C₂ × C₂` | X count and H count modulo two |
| 2 | `C₂ × C₂` | CX count and H count modulo two |
| 3 | `C₂ × C₂` | CCX count and H count modulo two |
| At least 4 | `C₂` | H count modulo two |

`LowWidthCharacters.agda` proves the displayed gate-count description
of the first three nontrivial rows.

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

## Natural rules

`Natural/` is a short local rule set for these gates, found by coset
enumeration (`../CCX+HH/Rules/naturalH2.py`). Besides the involutions it
has one rule on one wire and three on two:

| Rule | |
| --- | --- |
| `(X H)⁸ = 1` | the one-wire group is dihedral of order 16 |
| `XC X XC = X X↑` | X on the target of the reversed CNOT spreads to its control |
| `Ex H Ex = H↑` | the swap moves H to the other wire |
| `CZ XC CZ XC = Z` | CZ and the reversed CNOT commute up to Z |

Here `XC = H H↑ CX H↑ H` is the reversed CNOT, `Ex = CX XC CX` the swap,
`CZ = H CX H` and `Z = H X H`. The rules are sound at every width
(`Natural/Soundness`, through the complete translated calculus) and
complete on one and two wires (`Natural/Width1.agda`,
`Natural/Width2.agda`; on two wires the group is the real Clifford group
of order 2304). The completeness proof is a coset enumeration that proves
its own table, as for `CCX+HH/Natural`: every transition is a derivation
from the rules, checked by `Natural/Engine`'s `derive`, and the
representatives' matrices are distinct. The modules are generated by
`../CCX+HH/Rules/gen_width.py H N`; check them one by one: two wires is
87 modules and about 1¾ hours, the 35519 derivations in thirty `Facts`
modules (up to two minutes and 3.3 GB each) and the matrix checks in 49
`Agree` modules (half a minute each). `Width2/Tables`, `Sides` and the
assembly load every derivation: `Tables` needs about 5.5 GB, so give
those `+RTS -M7G`. From three wires on the group is infinite, so an
enumeration cannot certify completeness there.

`NaturalP/` adds the swap as a gate and the rules of
`CCX+HH/NaturalP` with HH written as H • H↑, together with its schema,
and one rule of its own, `CCXH⁴ : (CCX H)⁴ = CZ↑` (H on the target, CZ
on the controls), without which the rules are incomplete on three
wires (`Rules3/README.md`). The rules are sound at every width
(`NaturalP/Soundness`), and
complete at every width from four on given completeness of
`CCX+HH/NaturalP` on at most twelve wires (`NaturalP/Complete`): on
four or more wires every circuit is an HH circuit followed by H on
wire 0 or not (`NaturalP/Elim`), and the parity of the number of H
separates the two. On one and two wires completeness comes from
`Natural/` (`NaturalP/Bridge`). On three wires they are complete
(`NaturalP/ThreeWire/Complete.complete₃`): Clément's translation with a
decoder of our own, every decoded relation of Tables 1 and 2 derived by
a contraction in the graph of E8 lattices (`Rules3/`). So
`NaturalP/Three.every-width₃` is completeness at every width given
`CCX+HH/NaturalP`'s on four to twelve wires. Check
`NaturalP/Three.agda` module by module: `ThreeWire/Inst/` and
`ThreeWire/Disp/` are about 150 generated modules, each under five
minutes. `Rules3/README.md` and `../CCX+HH/Rules/README.md` have the
details.

## Reproduction

With Agda 2.8.0, standard-library 2.4 and EucDomain registered, run from
the repository root:

```sh
agda Examples/Groups/CCX+H/Presentation.agda
agda Examples/Groups/CCX+H/Orthogonal.agda
agda Examples/Groups/CCX+H/Structural.agda
agda Examples/Groups/CCX+H/Decision.agda
agda Examples/Groups/CCX+H/DecisionExamples.agda
agda Examples/Groups/CCX+H/Normalization.agda
agda Examples/Groups/CCX+H/GeneralN/HadamardParity.agda
agda Examples/Groups/CCX+H/GeneralN/Generation.agda
agda Examples/Groups/CCX+H/GeneralN/HadamardDecomposition.agda
agda Examples/Groups/CCX+H/GeneralN/HadamardAction.agda
agda Examples/Groups/CCX+H/GeneralN/SemidirectProduct.agda
agda Examples/Groups/CCX+H/GeneralN/NonNormal.agda
agda Examples/Groups/CCX+H/GeneralN/DihedralKernel.agda
agda Examples/Groups/CCX+H/GeneralN/ScaledAbelianization.agda
agda Examples/Groups/CCX+H/GeneralN/AmbientCosets.agda
agda Examples/Groups/CCX+H/GeneralN/Abelianization.agda
agda Examples/Groups/CCX+H/AbelianizationClassification.agda
agda Examples/Groups/CCX+H/LowWidthCharacters.agda
agda Examples/Groups/CCX+H/OneQubit.agda
agda Examples/Groups/CCX+H/OneQubitReduced.agda
agda Examples/Groups/CCX+H/TwoQubit.agda
agda Examples/Groups/CCX+H/ThreeQubit/Presentation.agda
agda Examples/Groups/CCX+H/ThreeQubit/Semantics.agda
agda Examples/Groups/CCX+H/Zero.agda
agda Examples/Groups/CCX+H/Certificates.agda
agda Examples/Groups/CCX+H/GeneralN/Presentation.agda
agda Examples/Groups/CCX+H/GeneralN/DyadicSchreier.agda
agda Examples/Groups/CCX+H/GeneralN/HadamardSchreier.agda
agda Examples/Groups/CCX+H/Natural/Width1.agda
agda Examples/Groups/CCX+H/Natural/Width2.agda
python3 -B Examples/Groups/CCX+H/TwoQubit/build_checks.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_decoding.py
python3 -B Examples/Groups/CCX+H/ThreeQubit/build_soundness.py
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 1 --check Examples/Groups/CCX+H/one_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 2 --check Examples/Groups/CCX+H/two_qubit_relations.json
python3 -B Examples/Groups/CCX+H/scripts/translated_relations.py --wires 3 --check Examples/Groups/CCX+H/three_qubit_relations.json
python3 -B Examples/Groups/CCX+H/GeneralN/construct.py --wires 4 --samples 4
python3 -B Examples/Groups/CCX+HH/Rules/gen_axiomsH.py --check
python3 -B Examples/Groups/CCX+HH/Rules/gen_width.py H 2 --check
```

The Python generators emit ordinary safe Agda definitions and proof
terms. Regeneration alone is not validation: rerun the Agda entry points
after generating them. No postulates or admitted holes are used.

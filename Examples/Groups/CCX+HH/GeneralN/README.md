# Physical decoding at width at least four

The files in this directory construct the physical circuits needed by the
four-coset Clément translation. Correctness is equality in the independent
ordinary matrix semantics of `../Semantics.agda`. All constructions retain
the input width and apply to every computational-basis state.

`Presentation.agda` proves soundness and completeness for ordinary
matrices at every width at least four. `DecodingPlans.agda` reduces the
four-state auxiliary edge generators to the three atoms below;
`Decoding.agda` realizes those plans as circuits and proves their matrices.
The final relations are the decoded auxiliary equations and one recovery
equation per physical generator, as in Clément's translation argument.

`Generation.agda` also identifies the physical image exactly. A source
word is realizable at this width precisely when its four-state charge is
00. `synthesize` returns the circuit and `correct` proves its matrix;
`necessary` proves the converse inclusion.

The three required auxiliary atoms have physical realizations:

| Auxiliary word | Circuit and matrix theorem |
| --- | --- |
| `M a • M b` | `CCX+H/GeneralN/SignPair.agda`, `circuit` and `correct`; equal indices are allowed |
| `X a b • X c d` | `DoubleExchange.agda`, module `Pair`; the exchanges may overlap or coincide |
| `(M a • X b c) • K a b c d` | `MixedPhysical.agda`, module `Block` |

The `CCX+H/GeneralN` modules in this table provide shared dyadic algebra
and routing. The resulting circuits use the `CCX+HH` alphabet.

## The circuit relations

Fix the wire count `w >= 4` and put `N = 2^w`. Let `q` be a two-level
generator and `c` one of the four charges. The auxiliary edge `(c,q)`
denotes `r(c) q r(c + charge(q))^-1`, with representatives
`r(00)=1`, `r(10)=M_0`, `r(11)=X_01`, and `r(01)=M_0 X_01`.
Reading a source word from charge `c` produces a word of edges, written
`F_c(u)`. Let `D` replace each edge by its physical circuit from
`Decoding.agda`, and let `E` be the structural physical-to-source encoder.
The following three finite families are the actual circuit axioms:

1. `D(F_c(u)) = D(F_c(v))` for every Table 1 instance `u = v` and every
   initial charge `c`.
2. `D([y]) = D(F_00(e(y)))` for every auxiliary edge `y`, where `e(y)` is
   its representative word above.
3. `[g] = D(F_00(E([g])))` for each primitive physical gate placement `g`.

The first two are `decoded (translated ...)` and
`decoded (roundtrip ...)`; the third is `recover` in the formal
presentation. Congruence, symmetry, transitivity, association, and unit
laws are supplied by the repository's presentation framework.

For a literal count before removing duplicate or redundant equations,
write `C(N,k)` for a binomial coefficient. Table 1 has

```text
R(N) = N + 4 C(N,2) + 5 C(N,3) + 10 C(N,4)
         + 9 C(N,5) + 16 C(N,6) + 71 C(N,8)
```

index instances, and its alphabet has `G(N) = N + C(N,2) + C(N,4)`
generators. The three families therefore have `4 R(N)`, `4 G(N)`, and
`4w-4` instances respectively. At four wires these are `4,410,824`,
`7,824`, and `12`: **4,418,660 raw circuit equations**. Order and
distinctness proof arguments are ignored by this count. The Agda
constructors represent the family without materializing millions of
long circuits; no claim of minimality is made. `relation_counts.py`
computes these counts for either gate set at any width at least four.

## Construction

`ControlledX.agda` compiles a controlled X with at most `width − 2`
controls. Its recursive commutator toggles a borrowed wire twice and
restores its original value. `BorrowedBit.agda` proves the Boolean
identity, `Placement.agda` routes each named gate into adjacent circuit
syntax, and `PlacementSemantics.agda` proves the resulting physical
matrix action. The borrowed wire can start in either state.

`ThreeCycleBase.agda` uses two such controlled gates to realize one
localized three-cycle. Its `outside` theorem fixes every other basis
state. `AffineRouting.agda` and `ThreeCycle.agda` move this cycle to any
three distinct basis levels. `BasisPermutations.agda` then decomposes
any pair of exchanges into at most two three-cycles, including all
overlap cases.

`PartialRouting.agda` routes any injective finite tuple of basis levels
to another injective tuple when two target levels remain unused. It
synthesizes transpositions, pairs them into physical circuits, and
absorbs an odd leftover by exchanging the two unused target levels.
This is used to transport the eight levels of a paired K block.

`SignPairBase.agda` starts from the four-level equation

```text
K₀₁₂₃ X₀₁ X₂₃ K₀₁₂₃ = M₁ M₃.
```

`LocalHadamard.agda` proves that this equation remains localized when
the surrounding physical HH acts on every spectator block. Those
other Hadamard blocks cancel. `PairRouting.agda` and the shared
permutation-conjugation theorem then place the two signs anywhere.

`KPairBase.agda` uses the eight-level equation

```text
S Q S Q S P = K₀₁₂₃ K₄₅₆₇,
S = M₀ M₄,  Q = K₀₁₂₃ K₄₅₆₇,  P = X₁₂ X₅₆.
```

In the physical circuit, `Q` is a single HH acting across the whole
width. `LocalEight.agda` proves that all complementary blocks cancel.
`CCX+H/GeneralN/KPairRouting.agda` transports the resulting two blocks
to arbitrary disjoint ordered quadruples. `LocalBlocks.agda` also gives
the general localization theorem for a block of size `2^(2+k)`.

Finally, `MixedPhysical.agda` chooses a level `e` and an ordered
quadruple `B` outside `A = (a,b,c,d)`. With

```text
Q = K_A K_B,  S = M_a M_e,
(Q S)² = M_a X_bc K_A.
```

The last identity is proved from the original two-level Table 1 in
`CCX+H/GeneralN/MixedAtom.agda`. `FiveFreshLevels.agda` constructs the
required fresh levels from the dimension bound. The only small matrix
calculations in this construction are the four- and eight-level base
identities; localization, routing, and the resulting arbitrary-width
matrix equalities are symbolic Agda proofs.

## Semantic bridge and checking

`BinaryBasis.agda` proves the correspondence between bit assignments
and finite basis indices. `BasisVectors.agda` connects these indices
to the tensor semantics. `ClassicalSemantics.agda` proves both the
vector action and every matrix column of an expanded classical circuit,
including the physical expansion of SWAP. `PhysicalEquality.agda`
transfers ordinary matrix equalities to vector-action equalities and
back.

`GateInvolutions.agda` proves that every physical generator squares to
the identity, at every width. Together with completeness this supplies
the group structure on the circuit presentation.

With Agda 2.8.0 and standard library 2.4, checking

```text
Examples/Groups/CCX+HH/GeneralN/Presentation.agda
```

reaches the complete physical construction and translation chain. `LocalBlocks.agda`
is an additional general theorem and can be checked separately.
Every Agda module uses `--safe`; the decoder has no postulates.

The executable `construct.py` is an independent exact-dyadic circuit
probe. Its checks at widths four, five, and six complement the symbolic
proofs; the presentation theorem uses the Agda constructions.

# Qudit Clifford circuits in odd prime dimension

Bian, Li, Ross, van de Wetering and Zhao, *A Complete and Natural Rule Set
for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions*,
arXiv:2609.40106. Formalized from the paper (TeX source and PDF),
independently of the Agda development.

## Statement

The paper's main result, Theorem 4.10, is stated about matrices: for every
odd prime `p`, the rules of Figure 1 only equate circuits that implement
the same linear map, and circuits that implement the same linear map are
equal by the rules. That is what is stated here (`theorem_4_10`, an
`IsSubPresentationOf` with the matrix semantics of Definition 2.11, at
symbolic `p` with `[Fact p.Prime]` and `p ≠ 2`).

| File | Contents | Paper |
| --- | --- | --- |
| `Syntax.lean` | gates `-ω`, `H`, `S`, `CZ`; derived generators `M_a` (T1), `X` (T2), `Z` (T3), `SWAP` (T4), `CX` (T6), remote `CZ` (T7); the rules `Rule.C0`–`Rule.C15` (`C3` a family over `k ∈ ℤ_p`), each on its own wires | Definition 2.11, Figures 1, 2 |
| `Semantics.lean` | `ω = e^{2πi/p}` (`ωℂ`), `λ_p = e^{(p-1)πi/4}` (`lambdaP`), the operators `Hop`, `Sop`, `CZop` on basis states `Fin n → Fin p`, their unitarity (`Hop_mem`: orthogonality of the characters of `ℤ_p`), `gateSem`, `sem p n` | Definitions 2.1, 2.5, 2.11 |
| `PathSum`, `Soundness`, `TwoQudit`, `Rules`, `ThreeQudit`, `Multiplier`, `GaussScalar` | soundness of every rule (below) | Proposition A.28, Lemmas A.15–A.27, 2.15, Proposition 2.13 |
| `Theory.lean` | `rule_sound`, `sound`, `grouplike` (`H_pow_four`) | Proposition A.28, Corollary A.8 |
| `Group.lean` | circuits modulo the rules as a group `CG p g n`, `semG`, the shift `ι` | |
| `SymplecticDef.lean`, `Symplectic.lean`, `SymplecticCalc.lean` | the action `σC` of circuits on Paulis modulo phases (`V p n`), its factorisation `σG` through the rules, its computation on shifted and padded circuits | §2.2.4 |
| `WeylOps.lean`, `Weyl.lean` | Weyl operators `weylOp v`; every circuit conjugates them as `σC` says, up to a nonzero scalar (`weylActs_sem`); distinct Weyl operators are not proportional; hence `sigma_of_sem` | §2.2.4 |
| `Pad.lean` | derivations on `k` wires hold on the bottom wires of `n + k` (`derives_pad`) | |
| `Quot.lean` | the quotient `Gh` by the Pauli normal closure, `σh`, `ιh`, `padh`, disjoint wires commute | §4.1 |
| `Schreier.lean` | Schreier's lemma for stabilisers | |
| `Sections.lean`, `Stab.lean` | the coset sections (inverses of the boxes `A`, `B` of Figure 6), the stabiliser chain `J`, `Kst`, `faith_succ` | §3.1 |
| `OneQudit.lean`, `Width1.lean` | the one-qudit calculus modulo Paulis (`Hq`, `Sq`, `Mq`; `M_a M_b = M_{ab}`, `M_a` conjugating `S`, `H` conjugating `M_a`); the stabiliser chain on one wire, `faith_one` | |
| `Transport.lean`, `Step.lean`, `Step2.lean` | the generators, sections and subgroups placed on the bottom wires; the induction step (`zstab_succ`, `xstab_succ`) from the local facts on two and three wires (`LF2`, `LF3`); `stab_all` | |
| `Width2Kit.lean`, `Width2.lean` | two qudits modulo Paulis: the swap, `CX`, `CX'`, the diagonal classes, `SWAP = H₁² CX CX'⁻¹ CX`; the local facts on two wires, `lf2` | |
| `Width3.lean` | three qudits modulo Paulis: the cycle of the wires ((C14), `cyc`), `CZ₀₁ CZ₁₂ = CZ₁₂ CZ₀₁` ((C15) conjugated by `S` on wire 1), (C15) moved by the cycle and the Steinberg relation of the `CX` gates; the local facts on three wires, `lf3` | |
| `Pauli.lean` | the Pauli subgroup `PauliSub`, its normal closure `PauliN` | §3.2, §4.2 |
| `SymplecticComplete.lean` | completeness up to Pauli corrections (`faith_all`, `symplectic_complete`) | Theorem 4.4 |
| `Projective.lean` | circuits modulo the rules and the scalars, `Gs`, `qs`, `ιs`, `pads`; disjoint wires commute, modulo the scalars and exactly in `CG` | |
| `PauliOne.lean` | one wire modulo the scalars: `H X H⁻¹ = Z`, `H Z H⁻¹ = X⁻¹`, `S Z = Z S`, `S X S⁻¹ = X Z`, `Z X = X Z`, `X^p = Z^p = 1`; the tactic `gnorm` (free-group normalisation) | Proposition 4.8 |
| `PauliTwo.lean` | two wires modulo the scalars: `CZ` commutes with `Z` on either wire and conjugates `X₀` to `X₀ Z₁`, `X₁` to `X₁ Z₀` | Proposition 4.8 |
| `PauliNormal.lean` | every gate conjugates every Pauli generator into the Pauli group (`conj_gen`); the Pauli group is normal, `pauli_normal` | Propositions 4.8, 4.9 |
| `PauliInj.lean` | Pauli normal forms `Wc v` implement the Weyl operators `W(v)`; modulo the scalars they exhaust the Pauli group; `pauli_inj` | Lemma 3.11 |
| `Theorem.lean` | `semG_injective`, `complete`, `theorem_4_10` | Theorem 4.10 |

Conventions (as in `QCert/QutritClifford`): the paper's top wire on `k`
wires is wire `k - 1`, its bottom wire wire `0`; `a ⨾ b` is `a` followed
by `b` (the word `b * a`); exponents of gates of order `p` and of `ω` are
elements of `ℤ_p` applied through `ZMod.val` (Remarks 1.1, 2.2: `S^{-1}` is
`S^{p-1}`, `a⁻¹` and fractions are computed in `ℤ_p`); the scalars `-1`
and `ω` are `(-ω)^p` and `(-ω)^{p+1}`; `(a/p)_L` is `legendreSym p a`,
entering `M_a` as `(-1)^{legendreExp p a}`. `g` is the generator of `ℤ_p^*`
chosen in Figure 1 (hypothesis `hg : ∀ a ≠ 0, ∃ k, g ^ k = a` where
completeness needs it).

Every rule, with these readings, was checked numerically (all of
C0–C15, every `k` of C3, and every `M_a` against `|x⟩ ↦ |ax⟩`) for
`p = 3, 5, 7` (three-wire rules for `p = 3, 5`) before being transcribed.

## Proved

* Unitarity of the gate matrices, so that the semantics is a monoid
  homomorphism into `U(pⁿ)` (`Semantics.lean`).
* **Soundness of all sixteen rules** (`rule_sound`, `sound`), at symbolic
  `p`, with no `sorry` of their own; (C2) and (C3) use Gauss's evaluation
  of the quadratic Gauss sum, `QCert.gauss_sum_sign`
  (`QCert/NumberTheory/GaussSign.lean`, proved by another development).
  `#print axioms` on `sound`, `rule_sound` and `grouplike` gives only
  `propext`, `Classical.choice` and `Quot.sound`. The path sums of
  Appendix A:
  * `PathSum.lean`: the character `ψ a = ω^a` of `ℤ_p` and
    `∑_u ψ(au) = p [a = 0]`; monomial operators `|t⟩ ↦ φ t |σ t⟩`,
    closed under products, shifts and padding.
  * `Soundness.lean`: (C0), (C1), (C6), (C8); Proposition 2.13
    `H² = λ_p⁻² M_{-1}` (`Hop_sq`) and (C5).
  * `TwoQudit.lean`: `λ_p² = (-1)^{(p-1)/2}`, `λ_p⁴ = 1`; Lemma A.20
    (`sem_SWAP`: (T4) is the swap) and Lemma A.18 (`sem_CX`).
  * `Rules.lean`: (C7), (C10), (C11), (C12); `ThreeQudit.lean`: (C13),
    (C14), (C15).
  * `Multiplier.lean`: Lemmas A.15, A.16 (`sem_Z`, `sem_X`); completing
    the square; `sem_M`: for `a ≠ 0` the circuit (T1) is a scalar `κ_a`
    times `|x⟩ ↦ |ax⟩` (one Gauss sum `G(a⁻¹/2)` in `κ_a`); (C4), (C9),
    which have one multiplier on each side.
  * `GaussScalar.lean`: `G(b) = (b/p) G(1)` (`G_mul`, from Mathlib's
    `quadraticChar_card_sqrts`), `λ_p = i^{(p-1)/2}`, and `κ_a = 1`
    (`κM_eq_one`, by `p mod 8` and `QCert.gauss_sum_sign`): Lemma 2.15
    (`sem_M_eq`); then (C2) and (C3) for every `k`.
* Every generator is invertible modulo the rules (`grouplike`): `(-ω)^{2p-1}`,
  `S^{p-1}`, `CZ^{p-1}` by (C0), (C1), (C6), and `H³` by `H_pow_four`, a
  derivation of `H⁴ = 1` (Corollary A.8) from (C2), (C3) and (C0) through
  `M_{-1} = M_g^{(p-1)/2}` (`g^{(p-1)/2} = -1` for a generator, by Euler's
  criterion) and `M_g^{p-1} = M_1 = M_g^0`; the scalar commutes with every
  generator by the structural rules (`scalar_comm`).

Soundness of (C2) and (C3) needs the sign of the Gauss sum: with
`M_a = κ P_a` (`κ = (2/p) λ_p⁻³ G(1)/√p`, independent of `a`, `κ² = 1`), (C2)
holds iff `κ = 1`, and (C3) says `κ^{k-1} = 1`, which for even `k` (and at
`k = 0`, `M_1 = 1`) is again `κ = 1`; `κ = 1` is Gauss's theorem.

## Completeness: the route

**`complete` and `theorem_4_10` are proved, with no `sorry`**:
`#print axioms QCert.QuditClifford.theorem_4_10` gives only `propext`,
`Classical.choice` and `Quot.sound`.  The proof (`Theorem.lean`) composes
four statements, the paper's Section 4.2 (`semG_injective`): equal matrices give equal actions
on Paulis (`sigma_of_sem`, proved: needs `p ≠ 2`, for `p = 2` the phase
gate is the identity matrix but not the identity action); equal actions give classes that differ by an
element of the normal closure of the Pauli group (`symplectic_complete`,
Theorem 4.4); that normal closure is the Pauli group (`pauli_normal`,
Proposition 4.9); and a Pauli circuit, scalar included, that implements
the identity is trivial (`pauli_inj`).

Theorem 4.4 is proved not through the paper's 42 box relations but by
a stabiliser chain, by induction on the number of wires, in the quotient by
the Pauli group: the stabiliser of `Z` on wire 0 is generated by circuits
on the other wires, `S` and `CZ` on wire 0 (stage 1), and within it the
stabiliser of `X` on wire 0 by circuits on the other wires (stage 2), each
by Schreier's lemma with explicit coset sections built from the paper's
normal boxes.  The generator cases reduce to the induction hypothesis and
a dozen local facts on one, two and three wires, derived from the rules
(`lf1`, `lf2`, `lf3`), all proved; `stab_all` then gives faithfulness at
every width (`faith_all`), which is Theorem 4.4 (`symplectic_complete`).
The three-wire facts (checked on symplectic matrices for `p = 3, 5, 7`
first) use (C14) and (C15) only, beside the two-wire facts: the cycle
`SWAP₀₁ SWAP₁₂` carries the classes on wires 0, 1 to those on wires 1, 2
((C14)), and (C15), conjugated by `S` on wire 1, gives the commutation of
`CZ₀₁` and `CZ₁₂` and, moved by the cycle, the Steinberg relation of the
`CX` gates.

The Pauli part (`pauli_normal`, `pauli_inj`) is derived modulo the
powers of the central scalar `-ω`, in `Gs` (`Projective.lean`), where the
phases drop out: a conjugate equal to a Pauli modulo the scalars is a
Pauli, the scalars being Paulis.  On one wire (`PauliOne.lean`) everything
follows from `H⁴ = 1`, (C1), (C5), the definitions (T2), (T3) of `X`, `Z`,
(C3) at `k = 0` with (T1) at `a = 1` (`(S H)³` is a scalar) and (C2) with
(T1) at `a = -1` (`H² = Z⁻¹ X S⁻¹ H S⁻¹ H S⁻¹ H` up to scalars), as in the
paper's proof of Proposition 4.8.  On two wires (`PauliTwo.lean`): `H²` on
wire 1 inverts `CZ` ((C2), (C3), (C9)); the swap moves this and (C8) to
wire 0; so `CZ` commutes with `Z = H² S H² S⁻¹` on either wire and
`CX = H₀⁻¹ CZ H₀` with `X` on its target; (C12) conjugated by `H²` on wire
1 gives `CX S₀ CX⁻¹`, whence `CX⁻¹ Z₀ CX = Z₁ Z₀`, and (C12) once more
gives `CZ X₀ CZ⁻¹ = X₀ Z₁`.  Every identity was checked on the unitaries
for `p = 3, 5, 7` first.  Modulo the scalars the normal forms
`⊗ᵢ Xᵢ^{aᵢ} Zᵢ^{bᵢ}` are a homomorphism from `ℤ_p^{2n}` onto the image of
the Pauli group, they implement the Weyl operators (`sem_Wc`), and a
power `(-ω)^K` is the identity only when `2p ∣ K`.

## Remaining `sorry`s

None.

## Errors in the paper

None found in Figure 1, Figure 2 or Definition 2.11: every rule holds as
printed for `p = 3, 5, 7`.

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
| `Theorem.lean` | `rule_sound`, `sound`, `complete`, `grouplike`, `theorem_4_10` | Theorem 4.10 |

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

## Remaining `sorry`s

| Name | Stands for |
| --- | --- |
| `complete` (`Theorem.lean`) | Theorem 4.10's completeness: Propositions 3.8 and 3.13 (normal forms), Theorem 4.4 (the 18 symplectic relations of Figure 9 are complete up to Pauli corrections, through the 42 box relations of Proposition 4.3; Figure 9's relations are derived from Figure 1 in the supplement), Propositions 4.8, 4.9 (lifting by Pauli corrections and scalars) |

## Errors in the paper

None found in Figure 1, Figure 2 or Definition 2.11: every rule holds as
printed for `p = 3, 5, 7`.

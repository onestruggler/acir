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
| `Soundness.lean` | soundness of (C0), (C1), (C6), (C8) | Corollaries A.13, A.14; Proposition A.28 |
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
  homomorphism into `U(pⁿ)` (`Semantics.lean`, no `sorry`).
* Soundness of (C0) `(-ω)^{2p} = 1`, (C1) `S^p = 1`, (C6) `CZ^p = 1` and
  (C8) (`Soundness.lean`, no `sorry`).
* The inverses of `-ω`, `S` and `CZ` modulo the rules (from C0, C1, C6).

## Remaining `sorry`s

| Name | Stands for |
| --- | --- |
| `rule_sound`, cases C2–C5, C7, C9–C15 (`Theorem.lean`) | Proposition A.28 (Lemmas A.25–A.27, path sums). C5, C7, C10–C15 need the matrices of `H²`, `SWAP` and `CX` (character sums over `ℤ_p`). C2, C3, C4, C9 involve the multiplier `M_a` (T1), whose matrix is `|x⟩ ↦ |ax⟩` exactly (Lemma 2.15) only by Gauss's evaluation of the quadratic Gauss sum `∑_j ω^{j²} = (2/p)_L λ_p⁻¹ √p`, sign included, which the paper cites and which Mathlib does not have (it has `gaussSum_sq`, not the sign). (C3) at `k = 0` says `M_1 = 1`, i.e. `H ⨾ S ⨾ H ⨾ S ⨾ H ⨾ S = ω^{-1/8}`, which is this evaluation. |
| `complete` (`Theorem.lean`) | Theorem 4.10's completeness: Propositions 3.8 and 3.13 (normal forms), Theorem 4.4 (the 18 symplectic relations of Figure 9 are complete up to Pauli corrections, through the 42 box relations of Proposition 4.3; Figure 9's relations are derived from Figure 1 in the supplement), Propositions 4.8, 4.9 (lifting by Pauli corrections and scalars) |
| `exists_inverse`, case `H` (`Theorem.lean`) | `H⁴ = 1` (Corollary A.8) is derivable from (C0), (C2), (C3) |

## Errors in the paper

None found in Figure 1, Figure 2 or Definition 2.11: every rule holds as
printed for `p = 3, 5, 7`.

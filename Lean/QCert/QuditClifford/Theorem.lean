/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits in odd prime dimension: Theorem 4.10

Bian, Li, Ross, van de Wetering and Zhao (arXiv:2609.40106), Theorem 4.10:
for every odd prime `p`, the rules of Figure 1 are sound and complete for
`n`-qudit Clifford circuits — they only equate circuits that implement the
same linear map, and circuits that implement the same linear map are equal
by the rules.  With every generator invertible modulo the rules, this is
`theorem_4_10`: the rules present the group of operators the circuits
denote (`IsSubPresentationOf`), the matrix semantics being part of the
statement.

`g` is the generator of `ℤ_p^*` chosen in Figure 1; soundness holds for any
`g ≠ 0`, completeness needs `g` to generate.  Soundness of every rule is
proved (Proposition A.28), (C2) and (C3) through Gauss's evaluation of the
quadratic Gauss sum (`QCert.gauss_sum_sign`).

Completeness follows the paper's Section 4.2: two circuits with the same
matrix act alike on Paulis (`sigma_of_sem`), so modulo the rules they differ
by an element of the normal closure of the Pauli group
(`symplectic_complete`, Theorem 4.4); that is the Pauli group itself
(`pauli_normal`, Proposition 4.9), on which the matrix semantics is
injective (`pauli_inj`).  The remaining `sorry`s are listed in
`README.md`.
-/
import QCert.QuditClifford.SymplecticComplete

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-- The matrix semantics is injective on circuits modulo the rules: the
composition of `sigma_of_sem` (equal matrices give equal actions on Paulis),
`symplectic_complete` (Theorem 4.4: equal actions give classes that differ by
an element of the normal closure of the Pauli group), `pauli_normal`
(Proposition 4.9: that normal closure is the Pauli group) and `pauli_inj`
(a Pauli circuit, scalar `(-ω)^t` included, that implements the identity is
trivial). -/
theorem semG_injective (g : ZMod p) [OddGen p g] (n : ℕ) :
    Function.Injective (semG (p := p) (g := g) n) := by
  intro a b h
  obtain ⟨w, rfl⟩ := mk_surjective n a
  obtain ⟨v, rfl⟩ := mk_surjective n b
  rw [semG_mk, semG_mk] at h
  set x := mk p g n w * (mk p g n v)⁻¹ with hx
  have hσ : σG n x = 1 := by
    have e : σG n (mk p g n w) = σG n (mk p g n v) := by
      rw [σG_mk, σG_mk, sigma_of_sem p h]
    rw [hx, map_mul, e, ← map_mul, mul_inv_cancel, map_one]
  have hs : semG n x = 1 := by
    rw [hx, map_mul, semG_mk, h, ← semG_mk (g := g), ← map_mul, mul_inv_cancel, map_one]
  have h1 := pauli_inj p g (pauli_normal p g n (symplectic_complete hσ)) hs
  rwa [hx, mul_inv_eq_one] at h1

/-- **Theorem 4.10, completeness**: two `n`-qudit circuits that implement the
same linear map are equal by the rules of Figure 1, for `g` a generator of
`ℤ_p^*`. -/
theorem complete (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    {n : ℕ} {w v : Circ n} (h : sem p n w = sem p n v) : Derives (Padded (Rule p g)) n w v := by
  haveI : OddGen p g := ⟨hp2, hg⟩
  rw [← mk_eq_mk]
  exact semG_injective p g n (by rw [semG_mk, semG_mk, h])

/-- **Theorem 4.10**: for every odd prime `p` and generator `g` of `ℤ_p^*`,
the rules of Figure 1 with the structural rules are sound and complete for
`n`-qudit Clifford circuits, at every `n`: they present the group of
operators that the circuits denote. -/
theorem theorem_4_10 (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    (n : ℕ) : IsSubPresentationOf (Theory p g n) ((gateSem p).gen (n := n)) where
  grouplike := grouplike p hp2 g hg n
  sound _ _ h := theory_sound p hp2 g (ne_zero_of_generates p hp2 g hg) h
  complete _ _ h := complete p hp2 g hg h

end QCert.QuditClifford

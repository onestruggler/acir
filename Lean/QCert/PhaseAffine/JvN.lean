/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The parallelogram law

A map `Q` from an abelian group `V` in which every element is a double, to
an abelian group `A` in which doubling is injective, satisfying the
parallelogram law `Q (u + v) + Q (u - v) = 2 Q u + 2 Q v`, has a biadditive
polar form `Q (u + v) - Q u - Q v` (the theorem of Jordan and von Neumann).
It is applied in `QuadDiag` to the quadratic phase atoms, whose
parallelogram law is rule (28) of Blake (arXiv:2603.06466).
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace QCert.PhaseAffine

variable {A V : Type*} [AddCommGroup A] [AddCommGroup V]

/-- The polar form of `Q`. -/
def polar (Q : V → A) (u v : V) : A := Q (u + v) + -Q u + -Q v

theorem polar_comm (Q : V → A) (u v : V) : polar Q u v = polar Q v u := by
  simp only [polar, add_comm u v]; abel

theorem Q_add_eq (Q : V → A) (u v : V) : Q (u + v) = Q u + Q v + polar Q u v := by
  simp only [polar]; abel

section JvN

variable (Q : V → A) (hdbl : ∀ x y : A, 2 • x = 2 • y → x = y)
  (hhalf : ∀ v : V, ∃ w, w + w = v) (htwo : ∀ v w : V, v + v = w + w → v = w)
  (hP : ∀ u v, Q (u + v) + Q (u - v) = 2 • Q u + 2 • Q v)

include hdbl hP in
theorem Q_zero : Q 0 = 0 := by
  have h := hP 0 0
  simp only [add_zero, sub_zero] at h
  apply hdbl
  rw [smul_zero]
  have : 2 • Q 0 + 2 • Q 0 = 2 • Q 0 + 0 := by rw [← h, add_zero, two_nsmul]
  exact add_left_cancel this

include hP in
/-- The polar form satisfies the parallelogram law in its first argument. -/
theorem polar_par (v a b : V) :
    polar Q (a + b) v + polar Q (a - b) v = 2 • polar Q a v := by
  have h1 := hP (a + v) b
  have h2 := hP a b
  calc polar Q (a + b) v + polar Q (a - b) v
      = (Q (a + v + b) + Q (a + v - b)) - (Q (a + b) + Q (a - b)) - 2 • Q v := by
        simp only [polar]
        rw [show a + b + v = a + v + b by abel, show a - b + v = a + v - b by abel]
        abel
    _ = (2 • Q (a + v) + 2 • Q b) - (2 • Q a + 2 • Q b) - 2 • Q v := by rw [h1, h2]
    _ = 2 • polar Q a v := by simp only [polar]; abel

include hdbl hhalf htwo hP in
/-- The theorem of Jordan and von Neumann: the polar form is additive in its
first argument. -/
theorem polar_add_left (u u' v : V) :
    polar Q (u + u') v = polar Q u v + polar Q u' v := by
  have h0 : polar Q 0 v = 0 := by simp [polar, Q_zero Q hdbl hP]
  obtain ⟨s, hs⟩ := hhalf (u + u')
  obtain ⟨t, ht⟩ := hhalf (u - u')
  have hst : s + t = u := htwo _ _ (by
    rw [show s + t + (s + t) = s + s + (t + t) by abel, hs, ht]; abel)
  have hst' : s - t = u' := htwo _ _ (by
    rw [show s - t + (s - t) = s + s - (t + t) by abel, hs, ht]; abel)
  have hd : polar Q (s + s) v = 2 • polar Q s v := by
    have := polar_par Q hP v s s
    rwa [sub_self, h0, add_zero] at this
  calc polar Q (u + u') v = polar Q (s + s) v := by rw [hs]
    _ = 2 • polar Q s v := hd
    _ = polar Q (s + t) v + polar Q (s - t) v := (polar_par Q hP v s t).symm
    _ = polar Q u v + polar Q u' v := by rw [hst, hst']

include hdbl hhalf htwo hP in
theorem polar_add_right (u v v' : V) :
    polar Q u (v + v') = polar Q u v + polar Q u v' := by
  rw [polar_comm, polar_add_left Q hdbl hhalf htwo hP, polar_comm Q v, polar_comm Q v']

include hdbl hhalf htwo hP in
theorem polar_nsmul_left (k : ℕ) (u v : V) : polar Q (k • u) v = k • polar Q u v := by
  induction k with
  | zero => simp [polar, Q_zero Q hdbl hP]
  | succ k ih => rw [succ_nsmul, polar_add_left Q hdbl hhalf htwo hP, ih, succ_nsmul]

include hdbl hhalf htwo hP in
theorem polar_nsmul_right (k : ℕ) (u v : V) : polar Q u (k • v) = k • polar Q u v := by
  rw [polar_comm, polar_nsmul_left Q hdbl hhalf htwo hP, polar_comm]

end JvN

/-! ### In a group, for commuting values -/

section Mul

variable {G : Type*} [Group G]

/-- The polar form in a group: `Q (u + v) Q(u)⁻¹ Q(v)⁻¹`. -/
def polarM (Q : V → G) (u v : V) : G := Q (u + v) * (Q u)⁻¹ * (Q v)⁻¹

variable (Q : V → G) (hcomm : ∀ u v, Commute (Q u) (Q v)) (m : ℕ) (hm : Odd m)
  (hexp : ∀ u, Q u ^ m = 1) (hhalf : ∀ v : V, ∃ w, w + w = v)
  (htwo : ∀ v w : V, v + v = w + w → v = w)
  (hP : ∀ u v, Q (u + v) * Q (u - v) = Q u ^ 2 * Q v ^ 2)

include hcomm in
theorem Q_add_eqM (u v : V) : Q (u + v) = Q u * Q v * polarM Q u v := by
  have h1 : Commute (Q u * Q v) (Q (u + v)) := (hcomm u (u + v)).mul_left (hcomm v (u + v))
  have h2 : (Q v)⁻¹ * (Q u)⁻¹ = (Q u)⁻¹ * (Q v)⁻¹ := ((hcomm u v).inv_inv).eq.symm
  simp only [polarM]
  calc Q (u + v) = Q (u + v) * (Q u * Q v) * ((Q v)⁻¹ * (Q u)⁻¹) := by group
    _ = Q u * Q v * Q (u + v) * ((Q u)⁻¹ * (Q v)⁻¹) := by rw [h1.eq, h2]
    _ = _ := by group

include hcomm hm hexp hhalf htwo hP in
/-- Jordan–von Neumann in a group, for commuting values of odd order. -/
theorem polarM_add_left (u u' v : V) :
    polarM Q (u + u') v = polarM Q u v * polarM Q u' v := by
  let H := Subgroup.closure (Set.range Q)
  letI : CommGroup H :=
    { (inferInstance : Group H) with
      mul_comm := (Subgroup.isMulCommutative_closure (by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact (hcomm a b).eq)).is_comm.comm }
  have hmem : ∀ a, Q a ∈ H := fun a => Subgroup.subset_closure ⟨a, rfl⟩
  let Qd : V → Additive H := fun a => Additive.ofMul ⟨Q a, hmem a⟩
  have hexpH : ∀ x : H, x ^ m = 1 := by
    rintro ⟨x, hx⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Subtype.ext (hexp a)
    | one => exact one_pow _
    | mul x y hx hy ihx ihy =>
      have := mul_pow (⟨x, hx⟩ : H) ⟨y, hy⟩ m
      rw [ihx, ihy, one_mul] at this
      exact this
    | inv x hx ih =>
      have := inv_pow (⟨x, hx⟩ : H) m
      rw [ih, inv_one] at this
      exact this
  have hdbl : ∀ x y : Additive H, 2 • x = 2 • y → x = y := by
    obtain ⟨k, hk⟩ := hm
    have hx : ∀ x : Additive H, x = (k + 1) • (2 • x) := by
      intro x
      have hmx : m • x = 0 := by
        apply Additive.toMul.injective
        rw [toMul_nsmul, hexpH, toMul_zero]
      calc x = m • x + x := by rw [hmx, zero_add]
        _ = (2 * k + 1 + 1) • x := by rw [hk, succ_nsmul x (2 * k + 1)]
        _ = (k + 1) • (2 • x) := by rw [smul_smul]; congr 1; ring
    intro x y h
    rw [hx x, hx y, h]
  have hP' : ∀ a b, Qd (a + b) + Qd (a - b) = 2 • Qd a + 2 • Qd b := by
    intro a b
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hP a b
  have h := polar_add_left Qd hdbl hhalf htwo hP' u u' v
  have e : ∀ a b, ((Additive.toMul (polar Qd a b) : H) : G) = polarM Q a b := fun a b => rfl
  rw [← e, ← e, ← e, h]
  rfl

include hcomm hm hexp hhalf htwo hP in
theorem polarM_add_right (u v v' : V) :
    polarM Q u (v + v') = polarM Q u v * polarM Q u v' := by
  have hsym : ∀ a b, polarM Q a b = polarM Q b a := by
    intro a b
    simp only [polarM, add_comm a b]
    rw [mul_assoc, mul_assoc, ((hcomm a b).inv_inv).eq]
  rw [hsym, polarM_add_left Q hcomm m hm hexp hhalf htwo hP, hsym v, hsym v']

end Mul


end QCert.PhaseAffine

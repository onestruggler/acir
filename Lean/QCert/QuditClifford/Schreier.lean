/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Schreier's lemma for stabilisers

Let a group act on a set through `act`, let `H` be the subgroup generated
by `S`, `y₀` a point and `s` a choice of an element for every point.  If
`s y₀` lies in a subgroup `K`, and for every generator `x` and every point
`y = h y₀` of the orbit the element `s (x y)⁻¹ x s y` lies in `K`, then
every element of `H` fixing `y₀` lies in `K`.  (The elements
`s (x y)⁻¹ x s y` are the Schreier generators of the stabiliser; that
they lie in `K` is the "box relations" of the paper.)
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

namespace QCert.QuditClifford

theorem schreier {G Y : Type*} [Group G] (act : G →* Function.End Y) (y₀ : Y) {K : Subgroup G}
    {S : Set G} (s : Y → G) (hs₀ : s y₀ ∈ K)
    (hstep : ∀ x ∈ S, ∀ h ∈ Subgroup.closure S,
      (s (act (x * h) y₀))⁻¹ * (x * s (act h y₀)) ∈ K) :
    ∀ h ∈ Subgroup.closure S, act h y₀ = y₀ → h ∈ K := by
  have hQ : ∀ x (hx : x ∈ Subgroup.closure S), ∀ h ∈ Subgroup.closure S,
      (s (act (x * h) y₀))⁻¹ * (x * s (act h y₀)) ∈ K := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hstep x hx
    | one => intro h _; simp
    | mul x y hx hy ihx ihy =>
      intro h hh
      have e : (s (act (x * y * h) y₀))⁻¹ * (x * y * s (act h y₀)) =
          ((s (act (x * (y * h)) y₀))⁻¹ * (x * s (act (y * h) y₀))) *
            ((s (act (y * h) y₀))⁻¹ * (y * s (act h y₀))) := by
        rw [mul_assoc x y h]; group
      rw [e]
      exact K.mul_mem (ihx (y * h) (Subgroup.mul_mem _ hy hh)) (ihy h hh)
    | inv x hx ihx =>
      intro h hh
      have key : (s (act (x⁻¹ * h) y₀))⁻¹ * (x⁻¹ * s (act h y₀)) =
          ((s (act (x * (x⁻¹ * h)) y₀))⁻¹ * (x * s (act (x⁻¹ * h) y₀)))⁻¹ := by
        rw [mul_inv_cancel_left]; group
      rw [key]
      exact K.inv_mem (ihx (x⁻¹ * h) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hh))
  intro h hh hfix
  have := hQ h hh 1 (Subgroup.one_mem _)
  rw [mul_one, map_one, hfix] at this
  change (s y₀)⁻¹ * (h * s y₀) ∈ K at this
  have h1 : s y₀ * ((s y₀)⁻¹ * (h * s y₀)) * (s y₀)⁻¹ = h := by group
  rw [← h1]
  exact K.mul_mem (K.mul_mem hs₀ this) (K.inv_mem hs₀)

end QCert.QuditClifford

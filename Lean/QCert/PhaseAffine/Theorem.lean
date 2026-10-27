/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of the phase-affine fragments

The main theorems of Blake, *Completeness for Prime-Dimensional Phase-Affine
Circuits* (arXiv:2603.06466), for a prime `d`:

* Theorem 1: the rules of Figure 1 (with the symmetry of the PROP) are
  complete for affine circuits, `Aff_d`, level `0`;
* Theorem 2 for each admissible fragment (Definition 12): `LinPhase_d`
  (level `1`, any prime `d`), `QuadPhase_d` (level `2`, `d` odd) and
  `CubicPhase_d` (level `3`, `d > 3`).

Each is stated as `IsSubPresentationOf`: the rules are sound for the matrix
semantics, circuits with the same matrix are equal in the theory, and every
generator is invertible in the theory; so the rule set presents the group
of unitaries the circuits generate.  The semantics is stated over any
commutative ring `A` with an involution and an injective additive
character `ψ : 𝔽_d → A` with `star (ψ a) = ψ (-a)` (`ψ a` stands for
`ω^a`); `ℂ` with `ω = e^{2πi/d}` is the instance `semℂ` (`theorem1ℂ`, …).

The matrix of a circuit determines its pair `(g, q)` (`pa_eq_of_sem`), so
completeness reduces to completeness for the pairs (`Completeness`).
-/
import QCert.PhaseAffine.Grouplike
import QCert.PhaseAffine.Completeness

namespace QCert.PhaseAffine

variable {d : ℕ} [Fact d.Prime] {A : Type*} [CommRing A] [StarRing A]
  (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a))

/-- With an injective character, circuits with the same matrix have the same
pair `(g, q)`. -/
theorem pa_eq_of_sem {lv : ℕ} (hinj : Function.Injective ψ) {n : ℕ} {w v : C d lv n}
    (h : FreeMonoid.lift ((sem lv ψ hψ).gen (n := n)) w =
      FreeMonoid.lift ((sem lv ψ hψ).gen (n := n)) v) :
    (gateData d lv).sem n w = (gateData d lv).sem n v := by
  have e : ((sem lv ψ hψ).sem n w).1 = ((sem lv ψ hψ).sem n v).1 := congrArg Subtype.val h
  rw [sem_val, sem_val] at e
  exact toOp_injective ψ hinj e

/-- A level whose pairs are complete is a sub-presentation of its matrices. -/
theorem isSubPresentation_of {lv : ℕ} (hA : Admissible d lv) (hinj : Function.Injective ψ)
    (hc : ∀ n (w v : C d lv n), (gateData d lv).sem n w = (gateData d lv).sem n v →
      Derivable (theory d lv n) w v) (n : ℕ) :
    IsSubPresentationOf (theory d lv n) ((sem lv ψ hψ).gen (n := n)) where
  grouplike := grouplike n
  sound _ _ h := theory_sound hA ψ hψ h
  complete _ _ h := hc n _ _ (pa_eq_of_sem ψ hψ hinj h)

section

variable (hinj : Function.Injective ψ)

include hinj

/-- Theorem 1: the affine circuits `Aff_d` (level `0`). -/
theorem theorem1 (n : ℕ) :
    IsSubPresentationOf (theory d 0 n) ((sem 0 ψ hψ).gen (n := n)) :=
  isSubPresentation_of ψ hψ admissible_zero hinj complete_lin0 n

/-- Theorem 2 for `LinPhase_d` (level `1`). -/
theorem theorem2_lin (n : ℕ) :
    IsSubPresentationOf (theory d 1 n) ((sem 1 ψ hψ).gen (n := n)) :=
  isSubPresentation_of ψ hψ admissible_one hinj complete_lin1 n

/-- Theorem 2 for `QuadPhase_d` (level `2`), `d` odd. -/
theorem theorem2_quad (hd : d ≠ 2) (n : ℕ) :
    IsSubPresentationOf (theory d 2 n) ((sem 2 ψ hψ).gen (n := n)) :=
  isSubPresentation_of ψ hψ (admissible_two hd) hinj (complete_quad hd) n

/-- Theorem 2 for `CubicPhase_d` (level `3`), `d > 3`. -/
theorem theorem2_cube (hd : 3 < d) (n : ℕ) :
    IsSubPresentationOf (theory d 3 n) ((sem 3 ψ hψ).gen (n := n)) :=
  isSubPresentation_of ψ hψ (admissible_three hd) hinj (complete_cube hd) n

end

/-- Theorem 1 over `ℂ`, `ω = e^{2πi/d}`. -/
theorem theorem1ℂ (n : ℕ) :
    IsSubPresentationOf (theory d 0 n) ((semℂ d 0).gen (n := n)) :=
  theorem1 _ _ ZMod.injective_stdAddChar n

/-- Theorem 2 for `LinPhase_d` over `ℂ`. -/
theorem theorem2_linℂ (n : ℕ) :
    IsSubPresentationOf (theory d 1 n) ((semℂ d 1).gen (n := n)) :=
  theorem2_lin _ _ ZMod.injective_stdAddChar n

/-- Theorem 2 for `QuadPhase_d` over `ℂ`, `d` odd. -/
theorem theorem2_quadℂ (hd : d ≠ 2) (n : ℕ) :
    IsSubPresentationOf (theory d 2 n) ((semℂ d 2).gen (n := n)) :=
  theorem2_quad _ _ ZMod.injective_stdAddChar hd n

/-- Theorem 2 for `CubicPhase_d` over `ℂ`, `d > 3`. -/
theorem theorem2_cubeℂ (hd : 3 < d) (n : ℕ) :
    IsSubPresentationOf (theory d 3 n) ((semℂ d 3).gen (n := n)) :=
  theorem2_cube _ _ ZMod.injective_stdAddChar hd n

end QCert.PhaseAffine

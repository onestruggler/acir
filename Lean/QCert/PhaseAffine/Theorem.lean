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
`ω^a`); `ℂ` with `ω = e^{2πi/d}` is the instance `semℂ`
(`theorem1ℂ`, …).
-/
import QCert.PhaseAffine.Semantics
import QCert.Presentation

namespace QCert.PhaseAffine

variable {d : ℕ} [Fact d.Prime] {A : Type*} [CommRing A] [StarRing A]
  (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a)) (hinj : Function.Injective ψ)

include hinj

/-- Theorem 1: the affine circuits `Aff_d` (level `0`). -/
theorem theorem1 (n : ℕ) :
    IsSubPresentationOf (theory d 0 n) ((sem 0 ψ hψ).gen (n := n)) := by
  sorry

/-- Theorem 2 for `LinPhase_d` (level `1`). -/
theorem theorem2_lin (n : ℕ) :
    IsSubPresentationOf (theory d 1 n) ((sem 1 ψ hψ).gen (n := n)) := by
  sorry

/-- Theorem 2 for `QuadPhase_d` (level `2`), `d` odd. -/
theorem theorem2_quad (hd : d ≠ 2) (n : ℕ) :
    IsSubPresentationOf (theory d 2 n) ((sem 2 ψ hψ).gen (n := n)) := by
  sorry

/-- Theorem 2 for `CubicPhase_d` (level `3`), `d > 3`. -/
theorem theorem2_cube (hd : 3 < d) (n : ℕ) :
    IsSubPresentationOf (theory d 3 n) ((sem 3 ψ hψ).gen (n := n)) := by
  sorry

end QCert.PhaseAffine

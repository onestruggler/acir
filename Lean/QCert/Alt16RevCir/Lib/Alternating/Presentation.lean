/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The circuit presentation of `𝔄ₙ`: Lafont's Theorem 4

Translation of `Examples/Groups/Alternating/Presentation.agda`.

Any sound theory in which the rules of Fig. 10 hold presents the group of
even permutations at every width.  `sem` is a monoid homomorphism by
definition, compatible with the congruence by soundness and injective by
completeness (Lemmas 6 and 8), so the circuits embed in `𝔄ₙ`
(`subpresentation_of`); by Lemma 6's existence half every even permutation
is a denotation (`Surjectivity`), which promotes the embedding to a
presentation (`presentation_of`).  `presentation` is the instance at
Theorem 4's three relations (p. 267).

The theorem for the alternating group `𝔄ₙ` alone is the one at width `n`:
the words over `Gn n` are those in `ω₁, …, ω_{n−2}`, and the structural
rules are the commutations `ω_i ω_j = ω_j ω_i`, `j > i + 2`.

**Order.**  Circuit words are in diagram order, and so is `sem`:
`sem (w * v) = sem v * sem w` (`sem_mul'`), the product of the Agda's
`Alt-group` (`∘ₚ`).  Mathlib's `alternatingGroup` multiplies in operator
order, so the Agda's group is its opposite: the presentations are stated in
`(Alt n)ᵐᵒᵖ`, a generator `g` read as `MulOpposite.op (semG g)` (`semOp`), so
that a circuit is read as `op` of its own even permutation (`lift_semOp`).
(`Gᵐᵒᵖ ≃* G` by inversion, `MulEquiv.inv'`.)

**Deviations from the Agda.**  The Agda builds a monoid sub-presentation
record (`submonoid-presentation-of`) and turns it into a sub-presentation by
`subMonoidPresentation⇒subPresentation`; the framework has no monoid
presentations, so `subpresentation_of` gives the fields directly (soundness,
completeness, `Fig10.grouplike`).  The Agda's module parameters `T`, `rules`
and `sound-T` are arguments.  `grouplike` (Theorem 4's relations are
grouplike) is added.  `presentation-Fig10` (the seven rules of Fig. 10 as
relations) and `presentation′` (`Alternative`'s relations) are not
translated.
-/
import QCert.Alt16RevCir.Lib.Alternating.Completeness
import QCert.Alt16RevCir.Lib.Alternating.Surjectivity

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

/-! ## Any sound theory with the rules of Fig. 10 presents `𝔄ₙ` -/

section Theory

variable {T : Theory} (rules : Fig10 T)
  (sound_T : ∀ {n : ℕ} {w v : Circ n}, T n w v → ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i)

include rules sound_T

/-- `sem` embeds the presented monoid, a group, in `𝔄ₙ`. -/
theorem subpresentation_of (n : ℕ) : IsSubPresentationOf (Lift T n) (semOp (n := n)) where
  grouplike := rules.grouplike n
  sound := fun w w' h => by
    rw [lift_semOp, lift_semOp, Alt.ext (sound_ax sound_T h)]
  complete := fun w w' h => by
    rw [lift_semOp, lift_semOp] at h
    exact Completeness.completeness rules sound_T fun i => by rw [MulOpposite.op_injective h]

/-- A sound theory with the rules of Fig. 10 presents `𝔄ₙ`. -/
theorem presentation_of (n : ℕ) : IsPresentationOf (Lift T n) (semOp (n := n)) where
  toIsSubPresentationOf := subpresentation_of rules sound_T n
  surjective := fun g => by
    obtain ⟨w, hw⟩ := surjective (T := T) (sound sound_T) g.unop
    exact ⟨w, by rw [lift_semOp, Alt.ext (hw w (Derivable.refl w)), MulOpposite.op_unop]⟩

end Theory

/-! ## Theorem 4 -/

/-- Theorem 4's relations are sound. -/
theorem soundness {n : ℕ} {w v : Circ n} (d : Derives SRel n w v) (i : Fin n) :
    Alt.perm (sem w) i = Alt.perm (sem v) i :=
  sound sound_S d i

/-- Theorem 4's relations are complete. -/
theorem completeness {n : ℕ} {w v : Circ n}
    (h : ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i) : Derives SRel n w v :=
  Completeness.completeness fig10 sound_S h

/-- Every generator is invertible modulo Theorem 4's relations. -/
theorem grouplike (n : ℕ) : Grouplike (Lift SRel n) := fig10.grouplike n

theorem subpresentation (n : ℕ) : IsSubPresentationOf (Lift SRel n) (semOp (n := n)) :=
  subpresentation_of fig10 sound_S n

/-- Lafont's Theorem 4: the cycle `ω` and the relations `order`, `near`,
`far`, with the structural rules, present the alternating group `𝔄ₙ` (in
diagram order). -/
theorem presentation (n : ℕ) : IsPresentationOf (Lift SRel n) (semOp (n := n)) :=
  presentation_of fig10 sound_S n

end QCert.Alt16RevCir.Alternating

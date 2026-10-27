/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness from an exact synthesis algorithm

An exact synthesis algorithm gives, for every element `M` of the group, a
*normal word* `nw M` that reduces `M` to the identity: `⟦nw M⟧ * M = 1`.
If the relations rewrite `nw (⟦x⟧ * M) * x` into `nw M` for every state `M`
and generator `x` (what a Main Lemma proves, by induction on the level of
`M`), then by induction on length every word `w` satisfies
`nw (⟦w⟧ * M) * w ≈ nw M`; two words with the same value then have the
same normal word after them, and cancelling it (the theory is grouplike)
shows they are equal in the theory: the relations present the group
(`NormalWords.isPresentationOf`).

`step_of_main_lemma` is the well-founded induction that turns a Main Lemma
— the square at `(M, x)` closes using only squares of smaller measure — into
the step for every state and generator.
-/
import QCert.Presentation

namespace QCert

universe u v

variable {X : Type u} {G : Type v} [Group G] {Γ : WRel X} {sem : X → G}

/-- Normal words of an exact synthesis algorithm. -/
structure NormalWords (Γ : WRel X) (sem : X → G) where
  /-- The normal word of a state. -/
  nw : G → Word X
  /-- It reduces the state to the identity. -/
  reduces : ∀ M, FreeMonoid.lift sem (nw M) * M = 1
  /-- One generator followed by the normal word of the new state is the
  normal word of the old one. -/
  step : ∀ M x, Derivable Γ (nw (sem x * M) * FreeMonoid.of x) (nw M)

namespace NormalWords

variable (N : NormalWords Γ sem)

/-- A whole word followed by the normal word of the state it reaches. -/
theorem word (w : Word X) (M : G) :
    Derivable Γ (N.nw (FreeMonoid.lift sem w * M) * w) (N.nw M) := by
  induction w using FreeMonoid.inductionOn' generalizing M with
  | one => simpa using Derivable.refl (N.nw M)
  | mul_of x w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, ← mul_assoc (N.nw _)]
    exact (Derivable.mul (N.step _ x) (Derivable.refl w)).trans (ih M)

include N in
/-- Grouplike relations whose normal words satisfy the step present the
group. -/
theorem isPresentationOf (grouplike : Grouplike Γ)
    (sound : ∀ ⦃w w' : Word X⦄, Γ w w' → FreeMonoid.lift sem w = FreeMonoid.lift sem w') :
    IsPresentationOf Γ sem where
  grouplike := grouplike
  sound := sound
  complete := by
    intro w v h
    -- every word has a left inverse modulo the theory
    have linv : ∀ a : Word X, ∃ b, Derivable Γ (b * a) 1 := by
      intro a
      induction a using FreeMonoid.inductionOn' with
      | one => exact ⟨1, by simpa using Derivable.refl (1 : Word X)⟩
      | mul_of x a ih =>
        obtain ⟨b, hb⟩ := ih
        obtain ⟨c, hc⟩ := grouplike x
        refine ⟨b * c, ?_⟩
        have : Derivable Γ (b * (c * FreeMonoid.of x) * a) (b * 1 * a) :=
          (Derivable.refl b).mul hc |>.mul (Derivable.refl a)
        simpa [mul_assoc] using this.trans (by simpa using hb)
    have hw := N.word w 1
    have hv := N.word v 1
    rw [mul_one] at hw hv
    rw [h] at hw
    obtain ⟨b, hb⟩ := linv (N.nw (FreeMonoid.lift sem v))
    have e : Derivable Γ (N.nw (FreeMonoid.lift sem v) * w) (N.nw (FreeMonoid.lift sem v) * v) :=
      hw.trans hv.symm
    have h1 : Derivable Γ w (b * (N.nw (FreeMonoid.lift sem v) * w)) := by
      simpa [mul_assoc] using (hb.mul (Derivable.refl w)).symm
    have h3 : Derivable Γ (b * (N.nw (FreeMonoid.lift sem v) * v)) v := by
      simpa [mul_assoc] using hb.mul (Derivable.refl v)
    exact h1.trans (((Derivable.refl b).mul e).trans h3)
  surjective := by
    intro M
    refine ⟨N.nw M⁻¹, ?_⟩
    have := N.reduces M⁻¹
    rw [mul_eq_one_iff_eq_inv, inv_inv] at this
    exact this

end NormalWords

/-- The well-founded induction behind a Main Lemma: if the step at `(M, x)`
follows from the steps of smaller measure, every step holds. -/
theorem step_of_main_lemma (nw : G → Word X) (μ : G → X → ℕ)
    (main : ∀ M x, (∀ M' x', μ M' x' < μ M x →
      Derivable Γ (nw (sem x' * M') * FreeMonoid.of x') (nw M')) →
      Derivable Γ (nw (sem x * M) * FreeMonoid.of x) (nw M)) :
    ∀ M x, Derivable Γ (nw (sem x * M) * FreeMonoid.of x) (nw M) := by
  intro M x
  induction h : μ M x using Nat.strong_induction_on generalizing M x with
  | _ k ih =>
    subst h
    exact main M x fun M' x' hlt => ih _ hlt M' x' rfl

end QCert

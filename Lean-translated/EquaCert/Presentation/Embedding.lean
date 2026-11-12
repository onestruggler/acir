/-
# Soundness and completeness of a presentation, and presentations carried
along a group monomorphism

Translation of `Presentation/Embedding.agda`.  A presentation is a
sub-presentation (`subpresentation`); the interpretation of a
sub-presentation is sound and complete (`Sub.sound`, `Sub.complete`, and
the same for a presentation, `Pres`); and an injective group homomorphism
`φ : G →* H` carries a sub-presentation of `G` to one of `H` whose
interpretation is `φ ∘ ⟦_⟧` (`along`, `along_presentation`).
-/
import EquaCert.Presentation.Definitions

namespace EquaCert

universe u v w

variable {X : Type u} {Γ : WRel X} {G : Type v} [Group G] {sem : X → G}

/-- A presentation is a sub-presentation (the Agda's `subpresentation`). -/
theorem subpresentation (p : IsPresentationOf Γ sem) : IsSubPresentationOf Γ sem :=
  p.toIsSubPresentationOf

namespace Sub

/-- The interpretation of a sub-presentation is sound (the Agda's
`Sub.sound`). -/
theorem sound (s : IsSubPresentationOf Γ sem) {w v : Word X} (d : Derivable Γ w v) :
    FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  derivable_sound s.sound d

/-- The interpretation of a sub-presentation is complete (the Agda's
`Sub.complete`). -/
theorem complete (s : IsSubPresentationOf Γ sem) {w v : Word X}
    (h : FreeMonoid.lift sem w = FreeMonoid.lift sem v) : Derivable Γ w v :=
  s.complete h

end Sub

namespace Pres

theorem sound (p : IsPresentationOf Γ sem) {w v : Word X} (d : Derivable Γ w v) :
    FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  Sub.sound (subpresentation p) d

theorem complete (p : IsPresentationOf Γ sem) {w v : Word X}
    (h : FreeMonoid.lift sem w = FreeMonoid.lift sem v) : Derivable Γ w v :=
  Sub.complete (subpresentation p) h

end Pres

section Along

variable {H : Type w} [Group H] (φ : G →* H) (φ_inj : Function.Injective φ)
include φ_inj

/-- A sub-presentation of `G` is one of `H` along an injective
homomorphism (the Agda's `along`). -/
theorem along (s : IsSubPresentationOf Γ sem) : IsSubPresentationOf Γ (φ ∘ sem) := by
  have key : ∀ w : Word X, FreeMonoid.lift (φ ∘ sem) w = φ (FreeMonoid.lift sem w) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | mul_of x w ih => simp [ih]
  refine ⟨s.grouplike, fun w w' h => ?_, fun w w' h => ?_⟩
  · rw [key, key, s.sound h]
  · rw [key, key] at h
    exact s.complete (φ_inj h)

/-- The Agda's `along-presentation`. -/
theorem along_presentation (p : IsPresentationOf Γ sem) : IsSubPresentationOf Γ (φ ∘ sem) :=
  along φ φ_inj (subpresentation p)

end Along

end EquaCert

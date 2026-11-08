------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of a congruence from soundness of its axioms, for a
-- reading of words into a monoid compared by _≡_ that is a monoid
-- homomorphism.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Congruence where

open import Relation.Binary.PropositionalEquality

open import Word.Base using (Word ; WRel ; ε ; _•_)
import Presentation.Base as PB

module Sound
  {X A : Set} (Γ : WRel X) (⟦_⟧ : Word X → A)
  (_∙_ : A → A → A) (e : A)
  (hom    : ∀ u w → ⟦ u • w ⟧ ≡ ⟦ u ⟧ ∙ ⟦ w ⟧)
  (unit   : ⟦ ε ⟧ ≡ e)
  (assoc  : ∀ a b c → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c))
  (idˡ    : ∀ a → e ∙ a ≡ a)
  (idʳ    : ∀ a → a ∙ e ≡ a)
  (sound-ax : ∀ {w v} → Γ w v → ⟦ w ⟧ ≡ ⟦ v ⟧)
  where

  open PB Γ using (_≈_)

  sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  sound PB.refl = refl
  sound (PB.sym h) = sym (sound h)
  sound (PB.trans h k) = trans (sound h) (sound k)
  sound (PB.cong {w} {w′} {v} {v′} h k) =
    trans (hom w v) (trans (cong₂ _∙_ (sound h) (sound k)) (sym (hom w′ v′)))
  sound (PB.assoc {w} {v} {u}) =
    trans (hom (w • v) u)
      (trans (cong (_∙ ⟦ u ⟧) (hom w v))
        (trans (assoc ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧)
          (trans (cong (⟦ w ⟧ ∙_) (sym (hom v u))) (sym (hom w (v • u))))))
  sound (PB.left-unit {w}) = trans (hom ε w) (trans (cong (_∙ ⟦ w ⟧) unit) (idˡ ⟦ w ⟧))
  sound (PB.right-unit {w}) = trans (hom w ε) (trans (cong (⟦ w ⟧ ∙_) unit) (idʳ ⟦ w ⟧))
  sound (PB.axiom a) = sound-ax a

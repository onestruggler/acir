------------------------------------------------------------------------
-- Presentations of groups
--
-- Oₙ(ℤ[1/√2]) is presented by the relations of Figure 6 of Fang,
-- Heunen and Kaarsgaard (Hadamard-Pi), and by Clément's relations.
--
-- Real-Clifford+CH-TwoLevel.Presentation proves the first given the
-- case of the Main Lemma that the paper's proof leaves open
-- (MainLemma.Hard); Hard proves that case, after Clément's Case 3.4.
-- The two sets of relations generate the same congruence
-- (Real-Clifford+CH-TwoLevel.Equivalence), so Clément's present the
-- group as well.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation {n : ℕ} where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
import Function.Bundles as Fun
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (grouplike)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma {n} using (Hard ; completeness-given)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation {n} as FHK
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence as EQ
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Hard as H

------------------------------------------------------------------------
-- The case the paper leaves open, at every level

hard : Hard
hard p k′ ℓ ih = H.hard p k′ ℓ ih

------------------------------------------------------------------------
-- Figure 6

presentation : (_===_ {n}) IsPresentationOf (O n)
presentation = FHK.presentation hard

------------------------------------------------------------------------
-- Clément's relations

private
  toᶜ : ∀ {u v : Word (Gen n)} → PB._≈_ (_===_ {n}) u v → PB._≈_ (_===ᶜ_ {n}) u v
  toᶜ = Fun.Equivalence.to EQ.equivalent

  fromᶜ : ∀ {u v : Word (Gen n)} → PB._≈_ (_===ᶜ_ {n}) u v → PB._≈_ (_===_ {n}) u v
  fromᶜ = Fun.Equivalence.from EQ.equivalent

monoidPresentationᶜ : (_===ᶜ_ {n}) IsMonoidPresentationOf (Group.monoid (O n))
monoidPresentationᶜ = record
  { ⟦_⟧ = FHK.⟦_⟧ᵒ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ h → sound-act (fromᶜ h) 𝕀 }
          ; homo = ⟦•⟧ᵐ
          }
        ; ε-homo = ≡.refl
        }
      ; injective = λ e → toᶜ (completeness-given hard e)
      }
    ; surjective = λ A → FHK.word-of A , λ z≈ → ≡.trans (sound-act (fromᶜ z≈) 𝕀) (FHK.word-of-correct A)
    }
  }

grouplikeᶜ : Grouplike (_===ᶜ_ {n})
grouplikeᶜ x = proj₁ (grouplike x) , toᶜ (proj₂ (grouplike x))

presentationᶜ : (_===ᶜ_ {n}) IsPresentationOf (O n)
presentationᶜ = monoidPresentation⇒presentation monoidPresentationᶜ grouplikeᶜ

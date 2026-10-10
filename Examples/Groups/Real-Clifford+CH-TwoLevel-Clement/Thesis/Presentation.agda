------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's theorem, by his own proof: Oₙ(ℤ[1/√2]) is presented by
-- his relations, and by those of Figure 6 of Hadamard-Pi.
--
-- * ⟦_⟧ is a homomorphism and respects the relations
--   (Real-Clifford+CH-TwoLevel.Soundness);
-- * it is onto: a matrix is the inverse of the output of Clément's
--   Algorithm 1 (Theorem 2.7, Algorithm.synthᶜ-correct);
-- * it is one-to-one on words modulo the relations (Theorem 4.1,
--   MainLemma.completeness, over the normal words of Algorithm 1).
--
-- The completeness is proved for the congruence of Figure 6, which is
-- that of Clément's relations (Real-Clifford+CH-TwoLevel.Equivalence).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Presentation {n : ℕ} where

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
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (grouplike ; _⁻¹ ; inverseˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence as EQ
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm using (synthᶜ ; synthᶜ-correct)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.MainLemma {n} using (completeness)

------------------------------------------------------------------------
-- The semantics in Oₙ(ℤ[1/√2]), onto by Clément's Algorithm 1

⟦_⟧ᵒ : Word (Gen n) → OMat n
⟦ w ⟧ᵒ = ⟦ w ⟧ᵐ , Unitary-⟦⟧ᵐ w

word-of : OMat n → Word (Gen n)
word-of (M , u) = synthᶜ M (→ColOrth (proj₁ u)) ⁻¹

word-of-correct : (A : OMat n) → ⟦ word-of A ⟧ᵐ ≡ proj₁ A
word-of-correct (M , u) =
  ≡.trans (≡.cong (actMʷ (w ⁻¹)) (≡.sym (synthᶜ-correct M (→ColOrth (proj₁ u))))) (sound-act (inverseˡ {w}) M)
  where
  w = synthᶜ M (→ColOrth (proj₁ u))

------------------------------------------------------------------------
-- Figure 6

monoidPresentation : (_===_ {n}) IsMonoidPresentationOf (Group.monoid (O n))
monoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ᵒ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ h → sound-act h 𝕀 }
          ; homo = ⟦•⟧ᵐ
          }
        ; ε-homo = ≡.refl
        }
      ; injective = completeness
      }
    ; surjective = λ A → word-of A , λ z≈ → ≡.trans (sound-act z≈ 𝕀) (word-of-correct A)
    }
  }

presentation : (_===_ {n}) IsPresentationOf (O n)
presentation = monoidPresentation⇒presentation monoidPresentation grouplike

------------------------------------------------------------------------
-- Clément's relations

private
  toᶜ : ∀ {u v : Word (Gen n)} → PB._≈_ (_===_ {n}) u v → PB._≈_ (_===ᶜ_ {n}) u v
  toᶜ = Fun.Equivalence.to EQ.equivalent

  fromᶜ : ∀ {u v : Word (Gen n)} → PB._≈_ (_===ᶜ_ {n}) u v → PB._≈_ (_===_ {n}) u v
  fromᶜ = Fun.Equivalence.from EQ.equivalent

monoidPresentationᶜ : (_===ᶜ_ {n}) IsMonoidPresentationOf (Group.monoid (O n))
monoidPresentationᶜ = record
  { ⟦_⟧ = ⟦_⟧ᵒ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ h → sound-act (fromᶜ h) 𝕀 }
          ; homo = ⟦•⟧ᵐ
          }
        ; ε-homo = ≡.refl
        }
      ; injective = λ e → toᶜ (completeness e)
      }
    ; surjective = λ A → word-of A , λ z≈ → ≡.trans (sound-act (fromᶜ z≈) 𝕀) (word-of-correct A)
    }
  }

grouplikeᶜ : Grouplike (_===ᶜ_ {n})
grouplikeᶜ x = proj₁ (grouplike x) , toᶜ (proj₂ (grouplike x))

presentationᶜ : (_===ᶜ_ {n}) IsPresentationOf (O n)
presentationᶜ = monoidPresentation⇒presentation monoidPresentationᶜ grouplikeᶜ

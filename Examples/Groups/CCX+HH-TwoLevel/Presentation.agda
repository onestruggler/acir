------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Table 1 present Oₙ(ℤ[1/2]) (Theorems 3.5, 4.3 and
-- 4.10).
--
-- * ⟦_⟧ is a homomorphism, and respects the relations (Soundness,
--   Theorem 4.3);
-- * it is onto: a matrix is the inverse of Algorithm 1's output
--   (Theorem 3.5);
-- * it is one-to-one on words modulo the relations (MainLemma,
--   Theorem 4.10).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH-TwoLevel.Presentation {n : ℕ} where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Word.Base using (Word)
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Synthesis using (synth ; synth-correct)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (grouplike ; _⁻¹ ; inverseˡ)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (sound-act)
open import Examples.Groups.CCX+HH-TwoLevel.MainLemma {n} using (completeness)

------------------------------------------------------------------------
-- The semantics in Oₙ(ℤ[1/2])

⟦_⟧ᵒ : Word (Gen n) → OMat n
⟦ w ⟧ᵒ = ⟦ w ⟧ᵐ , Unitary-⟦⟧ᵐ w

-- Every orthogonal matrix is a word's: the inverse of the output of
-- Algorithm 1.
word-of : OMat n → Word (Gen n)
word-of (M , u) = synth M (→ColOrth (proj₁ u)) ⁻¹

word-of-correct : (A : OMat n) → ⟦ word-of A ⟧ᵐ ≡ proj₁ A
word-of-correct (M , u) =
  ≡.trans (≡.cong (actMʷ (w ⁻¹)) (≡.sym (synth-correct M (→ColOrth (proj₁ u))))) (sound-act (inverseˡ {w}) M)
  where
  w = synth M (→ColOrth (proj₁ u))

------------------------------------------------------------------------
-- The presentation

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

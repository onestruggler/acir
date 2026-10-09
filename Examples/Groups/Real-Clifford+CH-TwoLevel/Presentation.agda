------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Figure 6 present Oₙ(ℤ[1/√2]) (Theorems 4.8, 4.13
-- and 4.14), given the case of the Main Lemma that the paper's proof
-- does not cover (MainLemma.Hard).
--
-- * ⟦_⟧ is a homomorphism, and respects the relations (Soundness,
--   Theorem 4.13);
-- * it is onto: a matrix is the inverse of Algorithm 1's output
--   (Theorems 4.8 and 4.10);
-- * it is one-to-one on words modulo the relations (Theorem 4.14),
--   given MainLemma.Hard.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation {n : ℕ} where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Synthesis using (synth ; synth-correct)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (grouplike ; _⁻¹ ; inverseˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma {n} using (Hard ; completeness-given)

open PB (_===_ {n}) using (_≈_)

------------------------------------------------------------------------
-- The semantics in Oₙ(ℤ[1/√2])

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
-- The presentation, given the hard case

module _ (hard : Hard) where

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
        ; injective = completeness-given hard
        }
      ; surjective = λ A → word-of A , λ z≈ → ≡.trans (sound-act z≈ 𝕀) (word-of-correct A)
      }
    }

  presentation : (_===_ {n}) IsPresentationOf (O n)
  presentation = monoidPresentation⇒presentation monoidPresentation grouplike

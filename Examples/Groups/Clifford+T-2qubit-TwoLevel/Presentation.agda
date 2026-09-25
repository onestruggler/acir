------------------------------------------------------------------------
-- Presentations of groups
--
-- The presentation theorem (Greylyn, "Generators and relations for the
-- group U₄(ℤ[1/√2,i])", the main theorem, with the exact synthesis
-- algorithm): in dimension n ≤ 4, the generators X_[a,b], H_[a,b] and
-- ω_[a] with the relations (1)–(20) of Table 1 present Uₙ(𝔻[ω]), the
-- group of unitary n × n matrices over 𝔻[ω] = ℤ[1/√2,i].
--
-- The semantics ⟦_⟧ᵘ takes a word to its matrix.  It is a monoid
-- homomorphism by soundness (Soundness, through Reduction.sound-act),
-- injective by completeness (MainLemma.relations-complete), and onto:
-- a unitary M is the matrix of the inverse of its normal word, which
-- takes M to I (Synthesis).  The relations being grouplike (Derived),
-- the monoid presentation is a group presentation.
--
-- Soundness and synthesis hold in every dimension; completeness uses
-- n ≤ 4 in one subcase of the Main Lemma (CaseXM).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Presentation {n : ℕ} where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Synthesis using (synth ; synth-correct)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n} using (grouplike ; _⁻¹ ; inverseˡ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (sound-act)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainLemma {n} using (relations-complete)

open PB (_===_ {n}) using (_≈_)

------------------------------------------------------------------------
-- The semantics

⟦_⟧ᵘ : Word (Gen n) → UMat n
⟦ w ⟧ᵘ = ⟦ w ⟧ᵐ , Unitary-⟦⟧ᵐ w

-- Every unitary is the matrix of a word: the inverse of its normal
-- word, which takes it to I.
word-of : UMat n → Word (Gen n)
word-of (M , u) = synth M (→ColOrth (proj₁ u)) ⁻¹

word-of-correct : (A : UMat n) → ⟦ word-of A ⟧ᵐ ≡ proj₁ A
word-of-correct (M , u) =
  ≡.trans (≡.cong (actMʷ (w ⁻¹)) (≡.sym (synth-correct M (→ColOrth (proj₁ u))))) (sound-act (inverseˡ {w}) M)
  where
  w = synth M (→ColOrth (proj₁ u))

------------------------------------------------------------------------
-- The presentation, in dimension at most 4

module _ (n≤4 : n ℕ.≤ 4) where

  monoidPresentation : (_===_ {n}) IsMonoidPresentationOf (Group.monoid (U n))
  monoidPresentation = record
    { ⟦_⟧ = ⟦_⟧ᵘ
    ; iso = record
      { isMonoidMonomorphism = record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = λ h → sound-act h 𝕀 }
            ; homo = ⟦•⟧ᵐ
            }
          ; ε-homo = ≡.refl
          }
        ; injective = relations-complete n≤4
        }
      ; surjective = λ A → word-of A , λ z≈ → ≡.trans (sound-act z≈ 𝕀) (word-of-correct A)
      }
    }

  -- The relations present Uₙ(𝔻[ω]), for n ≤ 4.
  presentation : (_===_ {n}) IsPresentationOf (U n)
  presentation = monoidPresentation⇒presentation monoidPresentation grouplike

------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics: the group Uₙ(𝔻[i]) of unitary n×n matrices over
-- 𝔻[i] = ℤ[½,i], as EucDomain matrices with EucDomain's product and
-- adjoint, and the matrices of the generators (§2.2 and §3.1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Instances using (adj)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties
  using (isCommutativeRing-DComplex ; adj-DComplex)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.Unitary as Unitary
import Examples.Groups.Clifford+CS-TwoLevel.EmbedAction as EmbedAction

------------------------------------------------------------------------
-- The constants: i is a unit, and |γ⁻¹|² = ½

ⅈ-unit : adj ⅈ DR.* ⅈ ≡ DR.1#
ⅈ-unit = refl

γ⁻-half : adj γ⁻ DR.* γ⁻ DR.+ adj γ⁻ DR.* γ⁻ ≡ DR.1#
γ⁻-half = refl

-- Everything of Action and Unitary, at 𝔻[i]: the generators act by
-- the one- and two-level matrices X_[a,b], K_[a,b] = γ⁻¹ [[1,1],[1,-1]]
-- at (a, b), and i_[a].
open Unitary isCommutativeRing-DComplex adj-DComplex ⅈ γ⁻ ⅈ-unit γ⁻-half public
open EmbedAction isCommutativeRing-DComplex adj-DComplex ⅈ γ⁻ ⅈ-unit γ⁻-half public

------------------------------------------------------------------------
-- The group Uₙ(𝔻[i])

-- Unitary matrices, compared by their entries.
UMat : ℕ → Set
UMat n = Σ (Matrix n n D) Unitary

U : ℕ → Group 0ℓ 0ℓ
U n = record
  { Carrier = UMat n
  ; _≈_     = λ A B → proj₁ A ≡ proj₁ B
  ; _∙_     = λ A B → proj₁ A ·*· proj₁ B , Unitary-·*· (proj₂ A) (proj₂ B)
  ; ε       = 𝕀 , Unitary-𝕀
  ; _⁻¹     = λ A → adjoint (proj₁ A) , Unitary-adjoint (proj₂ A)
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
          ; ∙-cong = cong₂ _·*·_
          }
        ; assoc = λ A B C → ·*·-assoc (proj₁ A) (proj₁ B) (proj₁ C)
        }
      ; identity = (λ A → ·*·-identityˡ (proj₁ A)) , (λ A → ·*·-identityʳ (proj₁ A))
      }
    ; inverse = (λ A → proj₁ (proj₂ A)) , (λ A → proj₂ (proj₂ A))
    ; ⁻¹-cong = cong adjoint
    }
  }

------------------------------------------------------------------------
-- The generators as elements of Uₙ(𝔻[i])

⟦_⟧₀ : ∀ {n} → Gen n → UMat n
⟦ g ⟧₀ = gmat g , Unitary-gmat g

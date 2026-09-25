------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics: the group Uₙ(𝔻[ω]) of unitary n×n matrices over
-- 𝔻[ω] = ℤ[1/√2,i], as EucDomain matrices with the (opaque) ring
-- operations of Ring, and the matrices of the generators: X_[a,b],
-- H_[a,b] = 1/√2 [[1,1],[1,-1]] at (a, b), and ω_[a].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Instances using (adj ; _+_ ; _*_ ; 1#)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.Unitary as Unitary
import Examples.Groups.Clifford+CS-TwoLevel.EmbedAction as EmbedAction

------------------------------------------------------------------------
-- The constants: ω is a unit, and |1/√2|² = ½

opaque
  unfolding _+ᴰ_ _*ᴰ_ adjᴰ

  ω-unit : adj ωᴰ * ωᴰ ≡ 1#
  ω-unit = refl

  √½-half : adj √½ * √½ + adj √½ * √½ ≡ 1#
  √½-half = refl

-- Everything of Action and Unitary, at 𝔻[ω]: the generators act by
-- the one- and two-level matrices X_[a,b], H_[a,b] and ω_[a].
open Unitary isCommutativeRing-D adj-D ωᴰ √½ ω-unit √½-half public
open EmbedAction isCommutativeRing-D adj-D ωᴰ √½ ω-unit √½-half public

------------------------------------------------------------------------
-- The group Uₙ(𝔻[ω])

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
-- The generators as elements of Uₙ(𝔻[ω])

⟦_⟧₀ : ∀ {n} → Gen n → UMat n
⟦ g ⟧₀ = gmat g , Unitary-gmat g

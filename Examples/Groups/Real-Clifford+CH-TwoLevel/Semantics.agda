------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics: the group Oₙ(ℤ[1/√2]) of orthogonal n×n matrices over
-- 𝔻[√2] = ℤ[1/√2] (Definition 4.3), as EucDomain matrices with the
-- (opaque) ring operations of Ring, and the matrices of the generators
-- (Definition 4.5): Z_[a] = -1 at a, X_[a,b] the transposition of a and
-- b, and H_[a,b] = 1/√2 [[1,1],[1,-1]] at (a, b).
--
-- The generic unitary machinery of Clifford+CS-TwoLevel applies with
-- the conjugation of 𝔻[√2], which is the identity, so its unitary
-- matrices are the orthogonal ones.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Instances using (adj ; _+_ ; _*_ ; 1#)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.Unitary as Unitary
import Examples.Groups.Clifford+CS-TwoLevel.EmbedAction as EmbedAction

------------------------------------------------------------------------
-- The constants: -1 is a unit, and (1/√2)² + (1/√2)² = 1

opaque
  unfolding _+ᴰ_ _*ᴰ_ adjᴰ

  -1-unit : adj -1ᴰ * -1ᴰ ≡ 1#
  -1-unit = refl

  √½-half : adj √½ * √½ + adj √½ * √½ ≡ 1#
  √½-half = refl

-- Everything of Action and Unitary, at 𝔻[√2]: the generators act by
-- the one- and two-level matrices Z_[a], X_[a,b] and H_[a,b].
open Unitary isCommutativeRing-D adj-D -1ᴰ √½ -1-unit √½-half public
open EmbedAction isCommutativeRing-D adj-D -1ᴰ √½ -1-unit √½-half public

------------------------------------------------------------------------
-- The group Oₙ(ℤ[1/√2])

-- Orthogonal matrices, compared by their entries.
OMat : ℕ → Set
OMat n = Σ (Matrix n n D) Unitary

O : ℕ → Group 0ℓ 0ℓ
O n = record
  { Carrier = OMat n
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
-- The generators as elements of Oₙ(ℤ[1/√2])

⟦_⟧₀ : ∀ {n} → Gen n → OMat n
⟦ g ⟧₀ = gmat g , Unitary-gmat g

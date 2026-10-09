------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics: the group Oₙ(ℤ[1/2]) of orthogonal n×n matrices over
-- 𝔻 = ℤ[1/2] (Definition 2.3), as EucDomain matrices with the (opaque)
-- ring operations of Ring, and the matrices of the generators of 𝒢ₙ
-- (Definition 2.6): (-1)_[a] = -1 at a, X_[a,b] the transposition of a
-- and b, and K_[a,b,c,d] = H ⊗ H = 1/2 [[1,1,1,1],[1,-1,1,-1],
-- [1,1,-1,-1],[1,-1,-1,1]] at (a, b, c, d) (Definition 2.4).
--
-- Conjugation on 𝔻 is the identity, so the unitary matrices are the
-- orthogonal ones.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Instances using (adj)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Orthogonal as Orthogonal
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction

-- Everything of Action and Orthogonal, at 𝔻 with h = 1/2: the
-- generators act by the one-, two- and four-level matrices (-1)_[a],
-- X_[a,b] and K_[a,b,c,d].
open Orthogonal isCommutativeRing-D adj-D ½ᴰ (adjᴰ-id ½ᴰ) ½-quarter public
open EmbedAction isCommutativeRing-D adj-D ½ᴰ public

------------------------------------------------------------------------
-- The group Oₙ(ℤ[1/2])

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
-- The generators as elements of Oₙ(ℤ[1/2])

⟦_⟧₀ : ∀ {n} → Gen n → OMat n
⟦ g ⟧₀ = gmat g , Unitary-gmat g

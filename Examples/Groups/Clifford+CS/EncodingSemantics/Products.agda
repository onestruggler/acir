------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of a product of two-level letters: the scalar
-- exponent adds up and the operators multiply
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Products (n : ℕ) where

open import Data.List using (List ; [] ; _∷_ ; foldr)
open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS.Numbering n using (N)
open import Examples.Groups.Clifford+CS.BridgeGray n using (⟦_⟧Y)

-- The exponents add up.
∏-ℓ : ∀ {A : Set} (cs : List A) (f : A → Word (TL.Gen N)) →
      proj₁ ⟦ ∏ cs f ⟧Y ≡ foldr (λ c k → proj₁ ⟦ f c ⟧Y +ℕ k) 0 cs
∏-ℓ []       f = Eq.refl
∏-ℓ (c ∷ cs) f = Eq.cong (proj₁ ⟦ f c ⟧Y +ℕ_) (∏-ℓ cs f)

-- The operators multiply, the first letter first.
∏-M : ∀ {A : Set} (cs : List A) (f : A → Word (TL.Gen N)) →
      proj₂ ⟦ ∏ cs f ⟧Y ≐ foldr (λ c M → proj₂ ⟦ f c ⟧Y ⊙ M) Idₒ cs
∏-M []       f = ≐-refl Idₒ
∏-M (c ∷ cs) f = ⊙-cong (≐-refl (proj₂ ⟦ f c ⟧Y)) (∏-M cs f)

-- A sum of exponents all zero.
sum-zero : ∀ {A : Set} (cs : List A) (f : A → Word (TL.Gen N)) →
           (∀ c → proj₁ ⟦ f c ⟧Y ≡ 0) → foldr (λ c k → proj₁ ⟦ f c ⟧Y +ℕ k) 0 cs ≡ 0
sum-zero []       f h = Eq.refl
sum-zero (c ∷ cs) f h = Eq.trans (Eq.cong₂ _+ℕ_ (h c) (sum-zero cs f h)) Eq.refl

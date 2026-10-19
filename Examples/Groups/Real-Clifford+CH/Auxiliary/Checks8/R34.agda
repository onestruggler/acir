------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (34), a pair of exchanges as two signed exchanges, decided on three qubits at the first indices 0 … 3 (4 … 7: R34Hi)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R34 where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (suc ; _∸_ ; _≤ᵇ_)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Word.Base using (ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)
open import Examples.Groups.Real-Clifford+CH.Encoding
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base

okR34₀ : ∀ b c d → (neqᵇ ₀ b ⇒ neqᵇ c d ⇒ decide (xx ₀ b c d) (zx ₀ ₀ b • zx b c d)) ≡ true
okR34₀ = all8₃-true (λ b c d → neqᵇ ₀ b ⇒ neqᵇ c d ⇒ decide (xx ₀ b c d) (zx ₀ ₀ b • zx b c d)) refl

okR34₁ : ∀ b c d → (neqᵇ ₁ b ⇒ neqᵇ c d ⇒ decide (xx ₁ b c d) (zx ₁ ₁ b • zx b c d)) ≡ true
okR34₁ = all8₃-true (λ b c d → neqᵇ ₁ b ⇒ neqᵇ c d ⇒ decide (xx ₁ b c d) (zx ₁ ₁ b • zx b c d)) refl

okR34₂ : ∀ b c d → (neqᵇ ₂ b ⇒ neqᵇ c d ⇒ decide (xx ₂ b c d) (zx ₂ ₂ b • zx b c d)) ≡ true
okR34₂ = all8₃-true (λ b c d → neqᵇ ₂ b ⇒ neqᵇ c d ⇒ decide (xx ₂ b c d) (zx ₂ ₂ b • zx b c d)) refl

okR34₃ : ∀ b c d → (neqᵇ ₃ b ⇒ neqᵇ c d ⇒ decide (xx ₃ b c d) (zx ₃ ₃ b • zx b c d)) ≡ true
okR34₃ = all8₃-true (λ b c d → neqᵇ ₃ b ⇒ neqᵇ c d ⇒ decide (xx ₃ b c d) (zx ₃ ₃ b • zx b c d)) refl

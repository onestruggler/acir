------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (32), two signed exchanges of consecutive indices commute, decided on three qubits at every first index
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R32 where

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

okR32₀ : ∀ a′ b b′ → (succᵇ ₀ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₀ ₀ a′ • zx b b b′) (zx b b b′ • zx ₀ ₀ a′)) ≡ true
okR32₀ = all8₃-true (λ a′ b b′ → succᵇ ₀ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₀ ₀ a′ • zx b b b′) (zx b b b′ • zx ₀ ₀ a′)) refl

okR32₁ : ∀ a′ b b′ → (succᵇ ₁ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₁ ₁ a′ • zx b b b′) (zx b b b′ • zx ₁ ₁ a′)) ≡ true
okR32₁ = all8₃-true (λ a′ b b′ → succᵇ ₁ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₁ ₁ a′ • zx b b b′) (zx b b b′ • zx ₁ ₁ a′)) refl

okR32₂ : ∀ a′ b b′ → (succᵇ ₂ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₂ ₂ a′ • zx b b b′) (zx b b b′ • zx ₂ ₂ a′)) ≡ true
okR32₂ = all8₃-true (λ a′ b b′ → succᵇ ₂ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₂ ₂ a′ • zx b b b′) (zx b b b′ • zx ₂ ₂ a′)) refl

okR32₃ : ∀ a′ b b′ → (succᵇ ₃ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₃ ₃ a′ • zx b b b′) (zx b b b′ • zx ₃ ₃ a′)) ≡ true
okR32₃ = all8₃-true (λ a′ b b′ → succᵇ ₃ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₃ ₃ a′ • zx b b b′) (zx b b b′ • zx ₃ ₃ a′)) refl

okR32₄ : ∀ a′ b b′ → (succᵇ ₄ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₄ ₄ a′ • zx b b b′) (zx b b b′ • zx ₄ ₄ a′)) ≡ true
okR32₄ = all8₃-true (λ a′ b b′ → succᵇ ₄ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₄ ₄ a′ • zx b b b′) (zx b b b′ • zx ₄ ₄ a′)) refl

okR32₅ : ∀ a′ b b′ → (succᵇ ₅ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₅ ₅ a′ • zx b b b′) (zx b b b′ • zx ₅ ₅ a′)) ≡ true
okR32₅ = all8₃-true (λ a′ b b′ → succᵇ ₅ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₅ ₅ a′ • zx b b b′) (zx b b b′ • zx ₅ ₅ a′)) refl

okR32₆ : ∀ a′ b b′ → (succᵇ ₆ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₆ ₆ a′ • zx b b b′) (zx b b b′ • zx ₆ ₆ a′)) ≡ true
okR32₆ = all8₃-true (λ a′ b b′ → succᵇ ₆ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₆ ₆ a′ • zx b b b′) (zx b b b′ • zx ₆ ₆ a′)) refl

okR32₇ : ∀ a′ b b′ → (succᵇ ₇ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₇ ₇ a′ • zx b b b′) (zx b b b′ • zx ₇ ₇ a′)) ≡ true
okR32₇ = all8₃-true (λ a′ b b′ → succᵇ ₇ a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx ₇ ₇ a′ • zx b b b′) (zx b b b′ • zx ₇ ₇ a′)) refl

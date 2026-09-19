------------------------------------------------------------------------
-- Presentations of groups
--
-- the Hadamard rules (35)–(37), decided on three qubits at the first indices 0 and 1
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H01 where

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

okRH₀ : ∀ b c d → (chkH′ (hpat (code₃ ₀) (code₃ b) (code₃ c) (code₃ d)) ₀ b c d) ≡ true
okRH₀ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₀) (code₃ b) (code₃ c) (code₃ d)) ₀ b c d) refl

okRH₁ : ∀ b c d → (chkH′ (hpat (code₃ ₁) (code₃ b) (code₃ c) (code₃ d)) ₁ b c d) ≡ true
okRH₁ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₁) (code₃ b) (code₃ c) (code₃ d)) ₁ b c d) refl

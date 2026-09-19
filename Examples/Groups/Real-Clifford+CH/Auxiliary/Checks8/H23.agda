------------------------------------------------------------------------
-- Presentations of groups
--
-- the Hadamard rules (35)–(37), decided on three qubits at the first indices 2 and 3
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H23 where

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

okRH₂ : ∀ b c d → (chkH′ (hpat (code₃ ₂) (code₃ b) (code₃ c) (code₃ d)) ₂ b c d) ≡ true
okRH₂ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₂) (code₃ b) (code₃ c) (code₃ d)) ₂ b c d) refl

okRH₃ : ∀ b c d → (chkH′ (hpat (code₃ ₃) (code₃ b) (code₃ c) (code₃ d)) ₃ b c d) ≡ true
okRH₃ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₃) (code₃ b) (code₃ c) (code₃ d)) ₃ b c d) refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- the Hadamard rules (35)–(37), decided on three qubits at the first indices 6 and 7
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H67 where

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

okRH₆ : ∀ b c d → (chkH′ (hpat (code₃ ₆) (code₃ b) (code₃ c) (code₃ d)) ₆ b c d) ≡ true
okRH₆ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₆) (code₃ b) (code₃ c) (code₃ d)) ₆ b c d) refl

okRH₇ : ∀ b c d → (chkH′ (hpat (code₃ ₇) (code₃ b) (code₃ c) (code₃ d)) ₇ b c d) ≡ true
okRH₇ = all8₃-true (λ b c d → chkH′ (hpat (code₃ ₇) (code₃ b) (code₃ c) (code₃ d)) ₇ b c d) refl

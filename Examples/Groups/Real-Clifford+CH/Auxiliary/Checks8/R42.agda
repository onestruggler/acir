------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (42), a Hadamard pair through two fresh indices, decided on three qubits at the first indices 0 … 3 (4 … 7: R42Hi)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R42 where

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

okR42₀ : ∀ b c d → (neqᵇ ₀ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₀) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₀ b c d)) ≡ true
okR42₀ = all8₃-true (λ b c d → neqᵇ ₀ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₀) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₀) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₀ b c d)) refl

okR42₁ : ∀ b c d → (neqᵇ ₁ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₁) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₁ b c d)) ≡ true
okR42₁ = all8₃-true (λ b c d → neqᵇ ₁ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₁) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₁) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₁ b c d)) refl

okR42₂ : ∀ b c d → (neqᵇ ₂ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₂) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₂ b c d)) ≡ true
okR42₂ = all8₃-true (λ b c d → neqᵇ ₂ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₂) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₂) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₂ b c d)) refl

okR42₃ : ∀ b c d → (neqᵇ ₃ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₃) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₃ b c d)) ≡ true
okR42₃ = all8₃-true (λ b c d → neqᵇ ₃ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₃) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₃) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₃ b c d)) refl

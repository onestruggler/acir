------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (42), a Hadamard pair through two fresh indices, decided on three qubits at the first indices 4 … 7 (0 … 3: R42)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R42Hi where

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

okR42₄ : ∀ b c d → (neqᵇ ₄ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₄) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₄ b c d)) ≡ true
okR42₄ = all8₃-true (λ b c d → neqᵇ ₄ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₄) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₄) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₄ b c d)) refl

okR42₅ : ∀ b c d → (neqᵇ ₅ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₅) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₅ b c d)) ≡ true
okR42₅ = all8₃-true (λ b c d → neqᵇ ₅ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₅) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₅) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₅ b c d)) refl

okR42₆ : ∀ b c d → (neqᵇ ₆ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₆) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₆ b c d)) ≡ true
okR42₆ = all8₃-true (λ b c d → neqᵇ ₆ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₆) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₆) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₆ b c d)) refl

okR42₇ : ∀ b c d → (neqᵇ ₇ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₇) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₇ b c d)) ≡ true
okR42₇ = all8₃-true (λ b c d → neqᵇ ₇ b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ {8} ₇) (toℕ b) (proj₁ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ {8} ₇) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh ₇ b c d)) refl

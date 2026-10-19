------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (34), a pair of exchanges as two signed exchanges, decided on three qubits at the first indices 4 … 7 (0 … 3: R34)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R34Hi where

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

okR34₄ : ∀ b c d → (neqᵇ ₄ b ⇒ neqᵇ c d ⇒ decide (xx ₄ b c d) (zx ₄ ₄ b • zx b c d)) ≡ true
okR34₄ = all8₃-true (λ b c d → neqᵇ ₄ b ⇒ neqᵇ c d ⇒ decide (xx ₄ b c d) (zx ₄ ₄ b • zx b c d)) refl

okR34₅ : ∀ b c d → (neqᵇ ₅ b ⇒ neqᵇ c d ⇒ decide (xx ₅ b c d) (zx ₅ ₅ b • zx b c d)) ≡ true
okR34₅ = all8₃-true (λ b c d → neqᵇ ₅ b ⇒ neqᵇ c d ⇒ decide (xx ₅ b c d) (zx ₅ ₅ b • zx b c d)) refl

okR34₆ : ∀ b c d → (neqᵇ ₆ b ⇒ neqᵇ c d ⇒ decide (xx ₆ b c d) (zx ₆ ₆ b • zx b c d)) ≡ true
okR34₆ = all8₃-true (λ b c d → neqᵇ ₆ b ⇒ neqᵇ c d ⇒ decide (xx ₆ b c d) (zx ₆ ₆ b • zx b c d)) refl

okR34₇ : ∀ b c d → (neqᵇ ₇ b ⇒ neqᵇ c d ⇒ decide (xx ₇ b c d) (zx ₇ ₇ b • zx b c d)) ≡ true
okR34₇ = all8₃-true (λ b c d → neqᵇ ₇ b ⇒ neqᵇ c d ⇒ decide (xx ₇ b c d) (zx ₇ ₇ b • zx b c d)) refl

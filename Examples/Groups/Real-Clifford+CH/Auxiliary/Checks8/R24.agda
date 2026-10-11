------------------------------------------------------------------------
-- Presentations of groups
--
-- the braid and the parity rules of the signed exchanges, Equations (24)–(28), decided on three qubits
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R24 where

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

ok24 : ∀ a a′ a″ → (succᵇ a a′ ⇒ succᵇ a′ a″ ⇒ decide (zx a a a′ • zx a′ a′ a″ • zx a a a′) (zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″)) ≡ true
ok24 = all8₃-true (λ a a′ a″ → succᵇ a a′ ⇒ succᵇ a′ a″ ⇒ decide (zx a a a′ • zx a′ a′ a″ • zx a a a′) (zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″)) refl

ok25 : ∀ a a′ c → (succᵇ a a′ ⇒ ltᵇ (toℕ a′) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) true ⇒ decide (zx a a c) (zx a′ a a′ • zx a′ a′ c • zx a a a′)) ≡ true
ok25 = all8₃-true (λ a a′ c → succᵇ a a′ ⇒ ltᵇ (toℕ a′) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) true ⇒ decide (zx a a c) (zx a′ a a′ • zx a′ a′ c • zx a a a′)) refl

ok26 : ∀ a a′ c → (succᵇ a a′ ⇒ ltᵇ (toℕ a′) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) true ⇒ decide (zx c a c) (zx a′ a a′ • zx c a′ c • zx a a a′)) ≡ true
ok26 = all8₃-true (λ a a′ c → succᵇ a a′ ⇒ ltᵇ (toℕ a′) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) true ⇒ decide (zx c a c) (zx a′ a a′ • zx c a′ c • zx a a a′)) refl

ok27 : ∀ a c′ c → (succᵇ c′ c ⇒ ltᵇ (suc (toℕ a)) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) false ⇒ decide (zx a a c) (zx c′ c′ c • zx a a c′ • zx c c′ c)) ≡ true
ok27 = all8₃-true (λ a c′ c → succᵇ c′ c ⇒ ltᵇ (suc (toℕ a)) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) false ⇒ decide (zx a a c) (zx c′ c′ c • zx a a c′ • zx c c′ c)) refl

ok28 : ∀ a c′ c → (succᵇ c′ c ⇒ ltᵇ (suc (toℕ a)) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) false ⇒ decide (zx c a c) (zx c′ c′ c • zx c′ a c′ • zx c c′ c)) ≡ true
ok28 = all8₃-true (λ a c′ c → succᵇ c′ c ⇒ ltᵇ (suc (toℕ a)) (toℕ c) ⇒ boolᵇ (parity (toℕ c ∸ toℕ a)) false ⇒ decide (zx c a c) (zx c′ c′ c • zx c′ a c′ • zx c c′ c)) refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- H_[0,1] H_[3,2] and the specific equations, (38)–(41) and (43)–(46), decided on three qubits
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R38 where

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

ok38 : ∀ a a′ → (succᵇ a a′ ⇒ (4 ≤ᵇ toℕ a) ⇒ decide (zx a a a′ • hh₀₁₃₂) (hh₀₁₃₂ • zx a a a′)) ≡ true
ok38 = all8₂-true (λ a a′ → succᵇ a a′ ⇒ (4 ≤ᵇ toℕ a) ⇒ decide (zx a a a′ • hh₀₁₃₂) (hh₀₁₃₂ • zx a a a′)) refl

ok39 : decide (zzℕ 0 1 • hh₀₁₃₂) (hh₀₁₃₂ • zzℕ 0 1) ≡ true
ok39 = refl

ok40 : decide (zzℕ 3 4 • hh₀₁₃₂) (hh₀₁₃₂ • zzℕ 3 4 • zxℕ 2 2 3) ≡ true
ok40 = refl

ok41 : decide (hh₀₁₃₂ • hh₀₁₃₂) ε ≡ true
ok41 = refl

ok43 : decide (hhℕ 0 1 3 2 • hhℕ 3 2 4 5) (xxℕ 0 3 1 2 • hhℕ 3 2 4 5 • xxℕ 0 3 1 2) ≡ true
ok43 = refl

ok44 : decide (xxℕ 0 3 1 2 • hhℕ 0 1 3 2) (hhℕ 0 1 3 2 • xxℕ 0 3 1 2) ≡ true
ok44 = refl

ok45 : decide (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6 • zzℕ 0 1 • hhℕ 0 3 1 2) (hhℕ 0 3 1 2 • zzℕ 0 1 • hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ≡ true
ok45 = refl

ok46 : decide (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • hhℕ 3 2 4 5 • hhℕ 7 6 4 5 • zzℕ 2 3 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2) (hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • zzℕ 2 3 • hhℕ 7 6 4 5 • hhℕ 3 2 4 5 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ≡ true
ok46 = refl

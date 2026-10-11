------------------------------------------------------------------------
-- Presentations of groups
--
-- the signs and the exchanges of consecutive indices, Equations (20)–(23), (29), (33), decided on three qubits
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R20 where

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

ok20 : ∀ a → (decide (zz a a) ε) ≡ true
ok20 = all8₁-true (λ a → decide (zz a a) ε) refl

ok21 : ∀ a b → (decide (zz a b) (zz b a)) ≡ true
ok21 = all8₂-true (λ a b → decide (zz a b) (zz b a)) refl

ok22 : ∀ a b c → (decide (zz a b • zz b c) (zz a c)) ≡ true
ok22 = all8₃-true (λ a b c → decide (zz a b • zz b c) (zz a c)) refl

ok23 : ∀ a a′ → (succᵇ a a′ ⇒ decide (zz a a′) (zx a a a′ • zx a a a′)) ≡ true
ok23 = all8₂-true (λ a a′ → succᵇ a a′ ⇒ decide (zz a a′) (zx a a a′ • zx a a a′)) refl

ok29 : ∀ a a′ → (succᵇ a a′ ⇒ decide (zx a a a′ • zx a′ a a′) ε) ≡ true
ok29 = all8₂-true (λ a a′ → succᵇ a a′ ⇒ decide (zx a a a′ • zx a′ a a′) ε) refl

ok33 : ∀ b a → (decide (zx b a b) (zx b b a)) ≡ true
ok33 = all8₂-true (λ b a → decide (zx b a b) (zx b b a)) refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- the other exchanges, Equations (30) and (31), decided on three qubits
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R30 where

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

ok30 : ∀ c a b → (neqᵇ a b ⇒ neqᵇ c a ⇒ neqᵇ c b ⇒ decide (zx c a b) (zz c a • zx a a b)) ≡ true
ok30 = all8₃-true (λ c a b → neqᵇ a b ⇒ neqᵇ c a ⇒ neqᵇ c b ⇒ decide (zx c a b) (zz c a • zx a a b)) refl

ok31 : ∀ a a′ c → (succᵇ a a′ ⇒ neqᵇ c a ⇒ neqᵇ c a′ ⇒ decide (zz a′ c • zx a a a′) (zx a a a′ • zz a c)) ≡ true
ok31 = all8₃-true (λ a a′ c → succᵇ a a′ ⇒ neqᵇ c a ⇒ neqᵇ c a′ ⇒ decide (zz a′ c • zx a a a′) (zx a a a′ • zz a c)) refl

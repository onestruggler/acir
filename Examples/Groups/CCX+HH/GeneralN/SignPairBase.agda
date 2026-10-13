------------------------------------------------------------------------
-- Presentations of groups
--
-- A localized pair of minus signs, in every width at least four.
-- HH conjugates (01)(23) in the first block into M1 M3; all other
-- Hadamard blocks cancel without assumptions on their inputs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.SignPairBase (n : ℕ) where

open import Data.Nat.Base using (suc ; _^_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; _•_)
open import Data.Fin.Base using (_<_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH.GeneralN.LocalHadamard
open import Examples.Groups.CCX+HH.GeneralN.PhysicalEquality using (matrix⇒action ; action⇒matrix)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
import Examples.Groups.CCX+HH.GeneralN.DoubleExchange as DE

width = suc (suc (suc (suc n)))
k = suc (suc n)

x-pair m-pair : Word (T.Gen 4)
x-pair = T.X ₀ ₁ (s≤s z≤n) • T.X ₂ ₃ (s≤s (s≤s (s≤s z≤n)))
m-pair = T.M ₁ • T.M ₃

opaque
  unfolding A.actV A.set₁ A.set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  base : A.⟦ [ K₀ ]ʷ • x-pair • [ K₀ ]ʷ ⟧ᵐ ≡ A.⟦ m-pair ⟧ᵐ
  base = refl

a = level k ₁
b = level k ₃
ordered : a < b
ordered = level-increasing k (s≤s (s≤s z≤n))

module Pair = DE.Pair n (level k ₀) (level k ₁) (level k ₂) (level k ₃)
  (level-increasing k (s≤s z≤n)) (level-increasing k (s≤s (s≤s (s≤s z≤n))))

private
  x-word : localized k x-pair ≡ Pair.auxiliary
  x-word = trans (localized-• k _ _)
    (cong₂ _•_ (localized-X k ₀ ₁ (s≤s z≤n)) (localized-X k ₂ ₃ (s≤s (s≤s (s≤s z≤n)))))

  m-word : localized k m-pair ≡ T.M a • T.M b
  m-word = trans (localized-• k _ _) (cong₂ _•_ (localized-M k ₁) (localized-M k ₃))

circuit : H.Circuit width
circuit = H.HH • Pair.circuit • H.HH

action : ∀ v → quantum circuit v ≡ A.actVʷ (T.M a • T.M b) v
action v = trans (cong (Q.hh k)
    (trans (matrix⇒action Pair.circuit Pair.auxiliary Pair.correct (Q.hh k v))
      (cong (λ w → A.actVʷ w (Q.hh k v)) (sym x-word))))
  (trans (conjugate-word k x-pair m-pair base v) (cong (λ w → A.actVʷ w v) m-word))

correct : Q.interpret circuit ≡ A.⟦ T.M a • T.M b ⟧ᵐ
correct = action⇒matrix circuit (T.M a • T.M b) action

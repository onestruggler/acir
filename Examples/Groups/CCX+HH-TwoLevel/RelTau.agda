------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's syllables, with a sign on each index, against the normal
-- syllables of Column, with one: on four indices written 0 < 1 < 2 < 3,
--
--   K (-1)_[0]^τ₀ (-1)_[1]^τ₁ (-1)_[2]^τ₂ (-1)_[3]^τ₃ = S′ K (-1)_[0]^t
--
-- with t = τ₀ xor τ₁ xor τ₂ xor τ₃ and S′ a word of X's and (-1)'s
-- (tauS), from (9a)–(9g) of Rel4 (Engine).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.RelTau where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Engine
open import Examples.Groups.CCX+HH-TwoLevel.TauSyl using (mτ)
open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.List.Base using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH-TwoLevel.Rel4 as R4

------------------------------------------------------------------------
-- Letters and axioms

private
  f0 f1 f2 f3 : Fin 4
  f0 = zero
  f1 = (suc zero)
  f2 = (suc (suc zero))
  f3 = (suc (suc (suc zero)))
  lt01 : f0 < f1
  lt01 = s≤s z≤n
  lt02 : f0 < f2
  lt02 = s≤s z≤n
  lt03 : f0 < f3
  lt03 = s≤s z≤n
  lt12 : f1 < f2
  lt12 = s≤s (s≤s z≤n)
  lt13 : f1 < f3
  lt13 = s≤s (s≤s z≤n)
  lt23 : f2 < f3
  lt23 = s≤s (s≤s (s≤s z≤n))
  k0123 : Gen 4
  k0123 = K-gen f0 f1 f2 f3 lt01 lt12 lt23
  m0 : Gen 4
  m0 = M-gen f0
  m1 : Gen 4
  m1 = M-gen f1
  m2 : Gen 4
  m2 = M-gen f2
  m3 : Gen 4
  m3 = M-gen f3
  x01 : Gen 4
  x01 = X-gen f0 f1 lt01
  x02 : Gen 4
  x02 = X-gen f0 f2 lt02
  x03 : Gen 4
  x03 = X-gen f0 f3 lt03
  x12 : Gen 4
  x12 = X-gen f1 f2 lt12
  x13 : Gen 4
  x13 = X-gen f1 f3 lt13
  x23 : Gen 4
  x23 = X-gen f2 f3 lt23

  ax-1b-m0-m0 : Eqn 4
  ax-1b-m0-m0 = ax⁼ (m0 ∷ m0 ∷ []) ([]) (r1b)

------------------------------------------------------------------------
-- The relations

tau-0000 : Eqn 4
tau-0000 = derive (k0123 ∷ []) (k0123 ∷ [])
  ( perm (k0123 ∷ [])
  ∷ perm (k0123 ∷ [])
  ∷ [] ) refl

tau-0001 : Eqn 4
tau-0001 = derive (k0123 ∷ m3 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m3 ∷ [])
  ∷ rw 1 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0123 ∷ m3 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9c)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-0010 : Eqn 4
tau-0010 = derive (k0123 ∷ m2 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m2 ∷ [])
  ∷ rw 1 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0123 ∷ m2 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9b)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-0011 : Eqn 4
tau-0011 = derive (k0123 ∷ m2 ∷ m3 ∷ []) (x02 ∷ x13 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m3 ∷ m2 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9f)
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ [])
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-0100 : Eqn 4
tau-0100 = derive (k0123 ∷ m1 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m1 ∷ [])
  ∷ rw 1 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0123 ∷ m1 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9a)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-0101 : Eqn 4
tau-0101 = derive (k0123 ∷ m1 ∷ m3 ∷ []) (x01 ∷ x23 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m3 ∷ m1 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9e)
  ∷ perm (x01 ∷ x23 ∷ k0123 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-0110 : Eqn 4
tau-0110 = derive (k0123 ∷ m1 ∷ m2 ∷ []) (x03 ∷ x12 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m2 ∷ m1 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9d)
  ∷ perm (x03 ∷ x12 ∷ k0123 ∷ [])
  ∷ perm (x03 ∷ x12 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-0111 : Eqn 4
tau-0111 = derive (k0123 ∷ m1 ∷ m2 ∷ m3 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 1 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ m0 ∷ [])
  ∷ rw 0 (sym⁼ R4.r9g)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-1000 : Eqn 4
tau-1000 = derive (k0123 ∷ m0 ∷ []) (k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m0 ∷ [])
  ∷ perm (k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-1001 : Eqn 4
tau-1001 = derive (k0123 ∷ m0 ∷ m3 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m3 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9c)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-1010 : Eqn 4
tau-1010 = derive (k0123 ∷ m0 ∷ m2 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m2 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9b)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-1011 : Eqn 4
tau-1011 = derive (k0123 ∷ m0 ∷ m2 ∷ m3 ∷ []) (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m3 ∷ m2 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9f)
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-1100 : Eqn 4
tau-1100 = derive (k0123 ∷ m0 ∷ m1 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m1 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9a)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ [])
  ∷ [] ) refl

tau-1101 : Eqn 4
tau-1101 = derive (k0123 ∷ m0 ∷ m1 ∷ m3 ∷ []) (x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m3 ∷ m1 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9e)
  ∷ perm (x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-1110 : Eqn 4
tau-1110 = derive (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ []) (x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ( perm (k0123 ∷ m2 ∷ m1 ∷ m0 ∷ [])
  ∷ rw 0 (rev⁼ R4.r9d)
  ∷ perm (x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ∷ perm (x03 ∷ x12 ∷ k0123 ∷ m0 ∷ [])
  ∷ [] ) refl

tau-1111 : Eqn 4
tau-1111 = derive (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ []) (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ( perm (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 0 (sym⁼ R4.r9g)
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ [] ) refl

------------------------------------------------------------------------
-- As a function of the signs

-- K on 0, 1, 2, 3.
K4 : Gen 4
K4 = k0123

tauS : Bool → Bool → Bool → Bool → List (Gen 4)
tauS false false false false = ([])
tauS false false false true = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ [])
tauS false false true false = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ [])
tauS false false true true = (x02 ∷ x13 ∷ [])
tauS false true false false = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
tauS false true false true = (x01 ∷ x23 ∷ [])
tauS false true true false = (x03 ∷ x12 ∷ [])
tauS false true true true = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
tauS true false false false = ([])
tauS true false false true = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x03 ∷ x12 ∷ [])
tauS true false true false = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x01 ∷ x23 ∷ [])
tauS true false true true = (x02 ∷ x13 ∷ [])
tauS true true false false = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
tauS true true false true = (x01 ∷ x23 ∷ [])
tauS true true true false = (x03 ∷ x12 ∷ [])
tauS true true true true = (m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])

tau-eqn : Bool → Bool → Bool → Bool → Eqn 4
tau-eqn false false false false = tau-0000
tau-eqn false false false true = tau-0001
tau-eqn false false true false = tau-0010
tau-eqn false false true true = tau-0011
tau-eqn false true false false = tau-0100
tau-eqn false true false true = tau-0101
tau-eqn false true true false = tau-0110
tau-eqn false true true true = tau-0111
tau-eqn true false false false = tau-1000
tau-eqn true false false true = tau-1001
tau-eqn true false true false = tau-1010
tau-eqn true false true true = tau-1011
tau-eqn true true false false = tau-1100
tau-eqn true true false true = tau-1101
tau-eqn true true true false = tau-1110
tau-eqn true true true true = tau-1111

tau-lhs : ∀ τ₀ τ₁ τ₂ τ₃ → lhs (tau-eqn τ₀ τ₁ τ₂ τ₃) ≡ K4 ∷ (mτ f0 τ₀ ++ (mτ f1 τ₁ ++ (mτ f2 τ₂ ++ mτ f3 τ₃)))
tau-lhs false false false false = refl
tau-lhs false false false true = refl
tau-lhs false false true false = refl
tau-lhs false false true true = refl
tau-lhs false true false false = refl
tau-lhs false true false true = refl
tau-lhs false true true false = refl
tau-lhs false true true true = refl
tau-lhs true false false false = refl
tau-lhs true false false true = refl
tau-lhs true false true false = refl
tau-lhs true false true true = refl
tau-lhs true true false false = refl
tau-lhs true true false true = refl
tau-lhs true true true false = refl
tau-lhs true true true true = refl

tau-rhs : ∀ τ₀ τ₁ τ₂ τ₃ → rhs (tau-eqn τ₀ τ₁ τ₂ τ₃) ≡ tauS τ₀ τ₁ τ₂ τ₃ ++ K4 ∷ mτ f0 (((τ₀ xor τ₁) xor τ₂) xor τ₃)
tau-rhs false false false false = refl
tau-rhs false false false true = refl
tau-rhs false false true false = refl
tau-rhs false false true true = refl
tau-rhs false true false false = refl
tau-rhs false true false true = refl
tau-rhs false true true false = refl
tau-rhs false true true true = refl
tau-rhs true false false false = refl
tau-rhs true false false true = refl
tau-rhs true false true false = refl
tau-rhs true false true true = refl
tau-rhs true true false false = refl
tau-rhs true true false true = refl
tau-rhs true true true false = refl
tau-rhs true true true true = refl

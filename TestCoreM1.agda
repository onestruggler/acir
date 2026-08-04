-- Throwaway computational validation of Keystone.core-M1 at p = 3.
-- NOT part of the library; delete after use.

module TestCoreM1 where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes ; ⌊_⌋)
open import Data.Bool using (Bool ; true ; _∧_)
import Data.List as L
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Fin using (Fin ; zero ; suc) renaming (_≟_ to _≟F_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

p-2 : ℕ
p-2 = 1

p-prime : Prime 3
p-prime = from-yes (prime? 3)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS p-2 p-prime
  using (mb-S)

------------------------------------------------------------------------
-- Local copies of the Keystone projections (Keystone has holes, so we
-- redefine the three one-liners instead of importing it).

mbSm : ∀ {k} → M (ℕ.suc k) → Vec B k → M (ℕ.suc k)
mbSm m bv = proj₁ (proj₂ (mb-S m bv))

mbv-M : ∀ {k} → M (ℕ.suc k) → Vec B k → Gen k → M (ℕ.suc k)
mbv-M m bv g = proj₁ (proj₂ (ML'T.mbv-push m bv g))

mbv-B : ∀ {k} → M (ℕ.suc k) → Vec B k → Gen k → Vec B k
mbv-B m bv g = proj₂ (proj₂ (ML'T.mbv-push m bv g))

------------------------------------------------------------------------
-- Decidable equality on the M column, to Bool.

eqZ : ℤ ₚ → ℤ ₚ → Bool
eqZ x y = ⌊ x ≟F y ⌋

eqD : D → D → Bool
eqD (a , b) (c , d) = eqZ a c ∧ eqZ b d

eqVD : ∀ {n} → Vec D n → Vec D n → Bool
eqVD [] [] = true
eqVD (x ∷ xs) (y ∷ ys) = eqD x y ∧ eqVD xs ys

eqM : ∀ {k} → M (ℕ.suc k) → M (ℕ.suc k) → Bool
eqM (vd , e) (vd' , e') = eqVD vd vd' ∧ eqZ e e'

check1 : ∀ {k} → M (ℕ.suc k) → Vec B k → Gen k → Bool
check1 m bv g = eqM (mbSm (mbv-M m bv g) (mbv-B m bv g)) (mbv-M (mbSm m bv) bv g)

------------------------------------------------------------------------
-- Enumeration at p = 3.

zp : L.List (ℤ ₚ)
zp = zero L.∷ suc zero L.∷ suc (suc zero) L.∷ L.[]

pairs : L.List (ℤ ₚ × ℤ ₚ)
pairs = L.concatMap (λ a → L.map (λ b → a , b) zp) zp

gens1 : L.List (Gen 1)
gens1 = gate₁ H-gate L.∷ gate₁ S-gate L.∷ L.[]

gens2 : L.List (Gen 2)
gens2 = gate₁ H-gate L.∷ gate₁ S-gate L.∷ gate₂ CZ-gate L.∷
        (gate₁ H-gate ↥) L.∷ (gate₁ S-gate ↥) L.∷ L.[]

-- k = 1: exhaustive (9 d × 3 e × 9 b × 2 gates = 486 instances).
test1 : Bool
test1 = L.and (L.concatMap (λ d → L.concatMap (λ e → L.concatMap (λ b →
          L.map (λ g → check1 ((d ∷ []) , e) (b ∷ []) g) gens1) pairs) zp) pairs)

t1 : test1 ≡ true
t1 = refl

-- k = 2: d₁, b₁ exhaustive; tail d₂, b₂ and e over samples; all 5 gates.
samples : L.List D
samples = (zero , zero) L.∷ (suc zero , suc (suc zero)) L.∷ (zero , suc zero) L.∷ L.[]

esamples : L.List E
esamples = zero L.∷ suc (suc zero) L.∷ L.[]

test2 : Bool
test2 = L.and
  (L.concatMap (λ d₁ → L.concatMap (λ b₁ → L.concatMap (λ d₂ → L.concatMap (λ b₂ →
   L.concatMap (λ e → L.map (λ g → check1 ((d₁ ∷ d₂ ∷ []) , e) (b₁ ∷ b₂ ∷ []) g) gens2)
   esamples) samples) samples) pairs) pairs)

t2 : test2 ≡ true
t2 = refl

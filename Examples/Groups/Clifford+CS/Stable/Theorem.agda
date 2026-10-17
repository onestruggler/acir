------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness at every width (the joint paper's Theorem S)
--
-- The induction on the width: completeness on 5 + m wires from
-- completeness on every width from five to 4 + m.  The inputs of the
-- gadget chain at index m — (F4) on 5 + m wires and the transport into
-- 5 + m wires — need completeness below 5 + m only, so they are given
-- under the bound `Below m` (Stable.Inputs): (F4) by Mixed.Reduce.Upto,
-- whose base facts at index k use completeness on 5 + k wires
-- (Base7/8/9's commutations), and the transport by Transport.Hyp, whose
-- commutation on 6 + k wires uses completeness on 5 + k.  Lemma87.step
-- then climbs one width (`complete`), and the bound is built along the
-- way (`below`).  The hypotheses are completeness on four wires (the
-- gadgets) and on five (`Five.Main.complete₅`, through Stable.Rules'
-- embedding).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

module Examples.Groups.Clifford+CS.Stable.Theorem (c4 : Complete 4) (c₅ : Completeᵧ 5) where

open import Data.Nat using (ℕ ; zero ; suc ; z≤n ; s≤s ; _≤_ ; _<_)
import Data.Nat.Properties as NP
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; Gate ; gate₁ ; gate₂ ; _↥ ; S-gate ; K-gate ; CS-gate)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ⁰ ; λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top1 ; top2)
open import Examples.Groups.Clifford+CS.Stable.Transport using (Hyp ; transportᵧ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Six)
open import Examples.Groups.Clifford+CS.Stable.Six.All using (six)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ) renaming (f5 to f5-all)
open import Examples.Groups.Clifford+CS.Stable.Mixed using (module Reduce)
open import Examples.Groups.Clifford+CS.Stable.Inputs using (Inputs ; Tr)
open import Examples.Groups.Clifford+CS.Five.Facts4Inst c4 using (facts4)
import Examples.Groups.Clifford+CS.Stable.Six.Mix1S as M1S
import Examples.Groups.Clifford+CS.Stable.Six.Mix1K as M1K
import Examples.Groups.Clifford+CS.Stable.Six.Mix2S as M2S
import Examples.Groups.Clifford+CS.Stable.Six.Mix2K as M2K
import Examples.Groups.Clifford+CS.Stable.Six.Mix3 as M3
import Examples.Groups.Clifford+CS.Stable.Base7 as B7
import Examples.Groups.Clifford+CS.Stable.Base8 as B8
import Examples.Groups.Clifford+CS.Stable.Base9 as B9
import Examples.Groups.Clifford+CS.Stable.Lemma87 as Lemma87

------------------------------------------------------------------------
-- The bound: completeness on the widths 5 … 4 + m

Below : ℕ → Set
Below m = ∀ k → k < m → Completeᵧ (₄₊ (suc k))

private
  down : ∀ {m} → Below (suc m) → Below m
  down h k lt = h k (NP.m≤n⇒m≤1+n lt)

  -- 6 + k ≤ 5 + m gives k < m.
  lt-of : ∀ {k m} → ₂₊ (₄₊ k) ≤ ₄₊ (suc m) → k < m
  lt-of (s≤s (s≤s (s≤s (s≤s (s≤s q))))) = q

------------------------------------------------------------------------
-- The inputs under the bound

-- (F4) at index m.
f4 : ∀ m → Below m → F4ᵗ m
f4 m h = Reduce.Upto.f4B c₅ b₁ b₂ m b₃ m NP.≤-refl
  where
  b₁ : (g : Gate 1) →
       (₂₊ (₄₊ zero)) ⊢ᵧ λ⁰ {suc zero} (gate₂ CS-gate ↥ ↥ ↥) • λ¹ {suc zero} (gate₁ g)
                       ≈ λ¹ {suc zero} (gate₁ g) • λ⁰ {suc zero} (gate₂ CS-gate ↥ ↥ ↥)
  b₁ S-gate = M1S.mix₁-S c₅
  b₁ K-gate = M1K.mix₁-K c₅

  b₂ : (g : Gate 1) →
       (₂₊ (₄₊ zero)) ⊢ᵧ λ⁰ {suc zero} (top1 4 g) • λ¹ {suc zero} (gate₂ CS-gate)
                       ≈ λ¹ {suc zero} (gate₂ CS-gate) • λ⁰ {suc zero} (top1 4 g)
  b₂ S-gate = M2S.mix₂-S c₅
  b₂ K-gate = M2K.mix₂-K c₅

  b₃ : ∀ k → k ≤ 3 → suc k ≤ m →
       (₂₊ (₄₊ k)) ⊢ᵧ λ⁰ {suc k} (top2 (₃₊ k) CS-gate) • λ¹ {suc k} (gate₂ CS-gate)
                    ≈ λ¹ {suc k} (gate₂ CS-gate) • λ⁰ {suc k} (top2 (₃₊ k) CS-gate)
  b₃ zero                      _ _  = M3.mix₃ c₅
  b₃ (suc zero)                _ lt = B7.mix-base-7 c₅ (h 1 lt)
  b₃ (suc (suc zero))          _ lt = B8.mix-base-8 c₅ (h 2 lt)
  b₃ (suc (suc (suc zero)))    _ lt = B9.mix-base-9 c₅ (h 3 lt)
  b₃ (suc (suc (suc (suc k)))) (s≤s (s≤s (s≤s ()))) _

-- The hypotheses of the transport into 5 + m wires.
hyp : ∀ m → Below m → Hyp (₄₊ (suc m))
hyp m h = record
  { complete₅   = c₅
  ; switch      = Six.switch S
  ; comm₁-base  = Six.comm₁-base S
  ; comm₂-base₁ = Six.comm₂-base₁ S
  ; comm₂-base₂ = base₂
  }
  where
  S = six c₅

  base₂ : ∀ k → k ≤ 3 → ₂₊ (₄₊ k) ≤ ₄₊ (suc m) →
          (₂₊ (₄₊ k)) ⊢ᵧ λ¹ {suc k} (top2 (₃₊ k) CS-gate) • λ¹ {suc k} (gate₂ CS-gate)
                       ≈ λ¹ {suc k} (gate₂ CS-gate) • λ¹ {suc k} (top2 (₃₊ k) CS-gate)
  base₂ zero                      _ _ = Six.comm₂-base₂ S
  base₂ (suc zero)                _ q = B7.comm₂-base₂₇ c₅ (h 1 (lt-of q))
  base₂ (suc (suc zero))          _ q = B8.comm₂-base₂-8 c₅ (h 2 (lt-of q))
  base₂ (suc (suc (suc zero)))    _ q = B9.comm₂-base₂-9 c₅ (h 3 (lt-of q))
  base₂ (suc (suc (suc (suc k)))) (s≤s (s≤s (s≤s ()))) _

-- The transport one wire up, at index m.
tr : ∀ m → Below m → Tr m
tr m h = transportᵧ (hyp m h) m NP.≤-refl

inputs : Inputs
inputs = record
  { Bnd  = Below
  ; down = down
  ; f4   = f4
  ; f5   = f5-all c₅
  ; tr   = tr
  }

------------------------------------------------------------------------
-- The induction

private
  module L = Lemma87 c4 c₅ inputs facts4

-- Completeness on 5 + m wires, given it below.
complete : ∀ m → Below m → Completeᵧ (₄₊ (suc m))
complete zero    _ = c₅
complete (suc m) h = L.step (suc m) h (h m NP.≤-refl)

-- The bound, at every index.
below : ∀ m → Below m
below zero    k ()
below (suc m) k (s≤s k≤m) with NP.m≤n⇒m<n∨m≡n k≤m
... | inj₁ k<m    = below m k k<m
... | inj₂ Eq.refl = complete k (below k)

-- Completeness on every width from five on.
completeᵧ : ∀ m → Completeᵧ (₄₊ (suc m))
completeᵧ m = complete m (below m)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The transport's hypotheses from completeness on five to eight wires
-- and seven equations on six
--
-- Stable.Transport carries derivations under the controlled functor at
-- every width given completeness on five wires and ten closed
-- equations (`Transport.Hyp`).  Three of them, on seven to nine wires,
-- follow from completeness one width down (Stable.Base7, Base8, Base9);
-- what is left is the seven on six wires (`Six`): the two borrowed-wire
-- switches, the CS on the top two wires of a five-wire domain against S
-- or K on wire 0, S or K on its top wire against the CS on the wires
-- 0 1, and the CS on its top two wires against the CS on the wires 0 1.
-- On six wires no borrowed-wire switch leaves a wire idle, so these are
-- the joint paper's derivations over the five-wire boxes (b6.py), which
-- Stable.Six derives from completeness on five wires (Stable.Six.All.six,
-- and hyp′ there: the transport from completeness alone).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.HypFrom where

open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Word.Base using (_•_)
import Data.Nat as ℕ
import Data.Nat.Properties as NP

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Coherence using (Switch₆)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top1 ; top2)
open import Examples.Groups.Clifford+CS.Stable.Transport using (Hyp)
import Examples.Groups.Clifford+CS.Stable.Base7 as B7
import Examples.Groups.Clifford+CS.Stable.Base8 as B8
import Examples.Groups.Clifford+CS.Stable.Base9 as B9

-- Completeness of the theory with the schema at a width.
Completeᵧ : ℕ → Set
Completeᵧ n = ∀ {u v : Circuit n} → ⟦ u ⟧ ~ ⟦ v ⟧ → n ⊢ᵧ u ≈ v

-- The seven equations on six wires.
record Six : Set where
  field
    switch      : Switch₆
    comm₁-base  : (h : Gate 1) →
                  (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥) • λ¹ {suc zero} (gate₁ h)
                                  ≈ λ¹ {suc zero} (gate₁ h) • λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥)
    comm₂-base₁ : (h : Gate 1) →
                  (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (top1 4 h) • λ¹ {suc zero} (gate₂ CS-gate)
                                  ≈ λ¹ {suc zero} (gate₂ CS-gate) • λ¹ {suc zero} (top1 4 h)
    comm₂-base₂ : (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (top2 (₃₊ zero) CS-gate) • λ¹ {suc zero} (gate₂ CS-gate)
                                  ≈ λ¹ {suc zero} (gate₂ CS-gate) • λ¹ {suc zero} (top2 (₃₊ zero) CS-gate)

-- Transport into at most N wires, from completeness on five wires and on
-- every width from six to below N.
hyp : ∀ N → Completeᵧ 5 → (∀ k → 6 ℕ.≤ k → k ℕ.< N → Completeᵧ k) → Six → Hyp N
hyp N c₅ below six = record
  { complete₅   = c₅
  ; switch      = Six.switch six
  ; comm₁-base  = Six.comm₁-base six
  ; comm₂-base₁ = Six.comm₂-base₁ six
  ; comm₂-base₂ = base₂
  }
  where
  6≤6 : 6 ℕ.≤ 6
  6≤6 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

  base₂ : ∀ m → m ℕ.≤ 3 → ₂₊ (₄₊ m) ℕ.≤ N →
          (₂₊ (₄₊ m)) ⊢ᵧ λ¹ {suc m} (top2 (₃₊ m) CS-gate) • λ¹ {suc m} (gate₂ CS-gate)
                       ≈ λ¹ {suc m} (gate₂ CS-gate) • λ¹ {suc m} (top2 (₃₊ m) CS-gate)
  base₂ zero                      _ _ = Six.comm₂-base₂ six
  base₂ (suc zero)                _ q = B7.comm₂-base₂₇ c₅ (below 6 6≤6 q)
  base₂ (suc (suc zero))          _ q = B8.comm₂-base₂-8 c₅ (below 7 (NP.m≤n⇒m≤1+n 6≤6) q)
  base₂ (suc (suc (suc zero)))    _ q = B9.comm₂-base₂-9 c₅ (below 8 (NP.m≤n⇒m≤1+n (NP.m≤n⇒m≤1+n 6≤6)) q)
  base₂ (suc (suc (suc (suc m)))) (s≤s (s≤s (s≤s ()))) _

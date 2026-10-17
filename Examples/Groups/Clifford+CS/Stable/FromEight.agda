------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness at every width, from completeness on five to eight wires
--
-- The λ-calculus at every width and the transport into every width
-- need completeness on five to eight wires and nothing else: (F4) is
-- MixAll.f4, (F5) is Calc.f5, and the hypotheses of the transport into
-- N wires (Transport.Hyp N) are completeness on five wires, the six-wire
-- equations (Six.All.six) and the commutations of Base7, Base8 and Base9,
-- which use completeness on six, seven and eight wires (`hyp₈`; HypFrom.
-- hyp asks for completeness on every width below N but uses only these).
-- So the inputs of the gadget chain are total, and Lemma87.step climbs
-- from five wires to every width (`complete`).  The bootstrap of six to
-- eight wires needs the chain with its inputs bounded by the width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

module Examples.Groups.Clifford+CS.Stable.FromEight
  (c4 : Complete 4) (c₅ : Completeᵧ 5) (c₆ : Completeᵧ 6) (c₇ : Completeᵧ 7) (c₈ : Completeᵧ 8)
  where

open import Data.Nat using (ℕ ; zero ; suc ; z≤n ; s≤s ; _≤_)
import Data.Nat.Properties as NP
open import Word.Base using (_•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; gate₂ ; CS-gate)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top2)
open import Examples.Groups.Clifford+CS.Stable.Transport using (Hyp ; transportᵧ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Six)
open import Examples.Groups.Clifford+CS.Stable.Six.All using (six)
open import Examples.Groups.Clifford+CS.Stable.MixAll using () renaming (f4 to f4-all)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ) renaming (f5 to f5-all)
open import Examples.Groups.Clifford+CS.Five.Facts4Inst c4 using (facts4)
import Examples.Groups.Clifford+CS.Stable.Base7 as B7
import Examples.Groups.Clifford+CS.Stable.Base8 as B8
import Examples.Groups.Clifford+CS.Stable.Base9 as B9
import Examples.Groups.Clifford+CS.Stable.Lemma87 as Lemma87

------------------------------------------------------------------------
-- The inputs

-- The hypotheses of the transport into any width.
hyp₈ : ∀ N → Hyp N
hyp₈ N = record
  { complete₅   = c₅
  ; switch      = Six.switch S
  ; comm₁-base  = Six.comm₁-base S
  ; comm₂-base₁ = Six.comm₂-base₁ S
  ; comm₂-base₂ = base₂
  }
  where
  S = six c₅

  base₂ : ∀ m → m ≤ 3 → ₂₊ (₄₊ m) ≤ N →
          (₂₊ (₄₊ m)) ⊢ᵧ λ¹ {suc m} (top2 (₃₊ m) CS-gate) • λ¹ {suc m} (gate₂ CS-gate)
                       ≈ λ¹ {suc m} (gate₂ CS-gate) • λ¹ {suc m} (top2 (₃₊ m) CS-gate)
  base₂ zero                      _ _ = Six.comm₂-base₂ S
  base₂ (suc zero)                _ _ = B7.comm₂-base₂₇ c₅ c₆
  base₂ (suc (suc zero))          _ _ = B8.comm₂-base₂-8 c₅ c₇
  base₂ (suc (suc (suc zero)))    _ _ = B9.comm₂-base₂-9 c₅ c₈
  base₂ (suc (suc (suc (suc m)))) (s≤s (s≤s (s≤s ()))) _

-- The transport, (F4) and (F5) at every width.
tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v
tr m = transportᵧ (hyp₈ (suc (₄₊ m))) m NP.≤-refl

f4 : ∀ m → F4ᵗ m
f4 = f4-all c₅ c₆ c₇ c₈

f5 : ∀ m → F5ᵗ m
f5 = f5-all c₅

------------------------------------------------------------------------
-- Completeness at every width

private
  module L = Lemma87 c4 c₅ f4 f5 tr facts4

-- Completeness on 5 + m wires.
complete : ∀ m → Completeᵧ (₄₊ (suc m))
complete zero    = c₅
complete (suc m) = L.step (suc m) (complete m)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The seven six-wire equations of the transport, from completeness on
-- five wires
--
-- Stable.HypFrom reduces the hypotheses of the transport at every width
-- to completeness on five wires and below N, and seven closed equations
-- on six wires (`Six`): the two borrowed-wire switches and the three
-- commutations whose λ-images cover every wire.  Here they are derived
-- from completeness on five wires, as the joint paper does (b6.py): the
-- S-box's box wire moves to an idle wire (Stable.Six.Su, by the box's
-- form t Q t Q and the swap of its box wire, Stable.Six.Dance), and the
-- rest are windows (Stable.Six.Switch, Comm1, Comm2, Comm3).  So the
-- transport into at most N wires needs completeness on five wires and on
-- every width from six below N, nothing else (`hyp′`, `transport′`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Six.All where

open import Data.Nat using (ℕ ; suc)
import Data.Nat as ℕ

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; S-gate ; K-gate)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Transport using (Hyp ; transportᵧ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ ; Six ; hyp)
import Examples.Groups.Clifford+CS.Stable.Six.Switch as SW
import Examples.Groups.Clifford+CS.Stable.Six.Comm1 as C1
import Examples.Groups.Clifford+CS.Stable.Six.Comm2 as C2
import Examples.Groups.Clifford+CS.Stable.Six.Comm3 as C3

six : Completeᵧ 5 → Six
six c₅ = record
  { switch      = record { sw₁₂ = SW.sw₁₂ c₅ ; sw₂₃ = SW.sw₂₃ c₅ }
  ; comm₁-base  = λ { S-gate → C1.comm₁-S c₅ ; K-gate → C1.comm₁-K c₅ }
  ; comm₂-base₁ = λ { S-gate → C2.comm₂-S c₅ ; K-gate → C2.comm₂-K c₅ }
  ; comm₂-base₂ = C3.comm₂₂ c₅
  }

-- The transport into at most N wires, from completeness on five wires and
-- on every width from six to below N.
hyp′ : ∀ N → Completeᵧ 5 → (∀ k → 6 ℕ.≤ k → k ℕ.< N → Completeᵧ k) → Hyp N
hyp′ N c₅ below = hyp N c₅ below (six c₅)

-- Hence the transport into at most N wires.
transport′ : ∀ N → Completeᵧ 5 → (∀ k → 6 ℕ.≤ k → k ℕ.< N → Completeᵧ k) →
             ∀ m → suc (₄₊ m) ℕ.≤ N → ∀ {u v : Circuit (₄₊ m)} →
             (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v
transport′ N c₅ below = transportᵧ (hyp′ N c₅ below)

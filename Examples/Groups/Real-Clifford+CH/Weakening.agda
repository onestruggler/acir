------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation between circuits holds on the bottom wires of any wider
-- circuit
--
-- A derivation on n wires is replayed on n + k wires, the k new wires
-- idle on top: each rule of Figure 4 is stated at every width above
-- its own, and the structural rules are natural in the width.  The one
-- exception is the schema (19), whose box holds every wire of its
-- width; it starts at five wires, so the statement is for n ≤ 4 —
-- which is what the paper's use of completeness at a lower width needs
-- (Lemma 7.6 inside three-qubit derivations, Lemmas D.3 and D.6 inside
-- four- and five-qubit ones).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Weakening where

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-trans ; n≤1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Syntactics

------------------------------------------------------------------------
-- Widening commutes with shifting

↑-↓ᵏ : ∀ {n} (w : Circuit n) k → (w ↑) ↓ᵏ k ≡ (w ↓ᵏ k) ↑
↑-↓ᵏ [ g ]ʷ  k = Eq.refl
↑-↓ᵏ ε       k = Eq.refl
↑-↓ᵏ (w • v) k = Eq.cong₂ _•_ (↑-↓ᵏ w k) (↑-↓ᵏ v k)

------------------------------------------------------------------------
-- The rules

private
  -- Figure 4 and the swap rules: the same rule at the wider width.
  weaken-srel : ∀ {n w v} k → n ≤ 4 → n SRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-srel k _ order-H       = PB.axiom (srel order-H)
  weaken-srel k _ order-Z       = PB.axiom (srel order-Z)
  weaken-srel k _ order-HZ      = PB.axiom (srel order-HZ)
  weaken-srel k _ order-CZ      = PB.axiom (srel order-CZ)
  weaken-srel k _ order-CH      = PB.axiom (srel order-CH)
  weaken-srel k _ merge-CZ      = PB.axiom (srel merge-CZ)
  weaken-srel k _ merge-CH      = PB.axiom (srel merge-CH)
  weaken-srel k _ comm-CZ-Ex    = PB.axiom (srel comm-CZ-Ex)
  weaken-srel k _ comm-CH-°CZ   = PB.axiom (srel comm-CH-°CZ)
  weaken-srel k _ slide-CH      = PB.axiom (srel slide-CH)
  weaken-srel k _ comm-CZ↑-CZ↓  = PB.axiom (srel comm-CZ↑-CZ↓)
  weaken-srel k _ comm-CZ↑-CH↓  = PB.axiom (srel comm-CZ↑-CH↓)
  weaken-srel k _ symm-controls = PB.axiom (srel symm-controls)
  weaken-srel k _ square-CCZX   = PB.axiom (srel square-CCZX)
  weaken-srel k _ comm-°CZ₂₀-CH = PB.axiom (srel comm-°CZ₂₀-CH)
  weaken-srel k _ comm-°CZ₂₀-HH = PB.axiom (srel comm-°CZ₂₀-HH)
  weaken-srel k _ conj-PP       = PB.axiom (srel conj-PP)
  weaken-srel k (s≤s (s≤s (s≤s (s≤s ())))) (box-Z j)
  weaken-srel k _ swap-order    = PB.axiom (srel swap-order)
  weaken-srel k _ swap-Z        = PB.axiom (srel swap-Z)
  weaken-srel k _ swap-H        = PB.axiom (srel swap-H)
  weaken-srel k _ swap-CZ       = PB.axiom (srel swap-CZ)
  weaken-srel k _ swap-CH       = PB.axiom (srel swap-CH)

  -- With the structural rules.
  weaken-ax : ∀ {n w v} k → n ≤ 4 → n VRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-ax k le (srel a)                  = weaken-srel k le a
  weaken-ax k le (cong↑ {w = w} {v = v} a) =
    Eq.subst₂ (λ x y → _ ⊢ x ≈ y) (Eq.sym (↑-↓ᵏ w k)) (Eq.sym (↑-↓ᵏ v k))
      (lemma-cong↑ (w ↓ᵏ k) (v ↓ᵏ k) (weaken-ax k (≤-trans (n≤1+n _) le) a))
  weaken-ax k le (comm₁ h g)               = PB.axiom (comm₁ h (g ↧ᵏ k))
  weaken-ax k le (comm₂ h g)               = PB.axiom (comm₂ h (g ↧ᵏ k))
  weaken-ax k le (ω↑=ω ())

------------------------------------------------------------------------
-- The congruence

weaken : ∀ {n w v} k → n ≤ 4 → n ⊢ w ≈ v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
weaken k le PB.refl        = PB.refl
weaken k le (PB.sym e)     = PB.sym (weaken k le e)
weaken k le (PB.trans e f) = PB.trans (weaken k le e) (weaken k le f)
weaken k le (PB.cong e f)  = PB.cong (weaken k le e) (weaken k le f)
weaken k le PB.assoc       = PB.assoc
weaken k le PB.left-unit   = PB.left-unit
weaken k le PB.right-unit  = PB.right-unit
weaken k le (PB.axiom a)   = weaken-ax k le a

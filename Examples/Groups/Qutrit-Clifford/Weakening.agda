------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation between circuits holds on the bottom wires of any wider
-- circuit
--
-- A derivation on n wires is replayed on n + k wires, the k new wires
-- idle on top: each of the rules C₁–C₁₈ is stated at every width above
-- its own, and the structural rules are natural in the width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Weakening where

open import Data.Nat.Base using (ℕ ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Qutrit-Clifford.Syntactics

------------------------------------------------------------------------
-- Widening commutes with shifting

↑-↓ᵏ : ∀ {n} (w : Circuit n) k → (w ↑) ↓ᵏ k ≡ (w ↓ᵏ k) ↑
↑-↓ᵏ [ g ]ʷ  k = Eq.refl
↑-↓ᵏ ε       k = Eq.refl
↑-↓ᵏ (w • v) k = Eq.cong₂ _•_ (↑-↓ᵏ w k) (↑-↓ᵏ v k)

------------------------------------------------------------------------
-- The rules

private
  weaken-qrel : ∀ {n w v} k → n QRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-qrel k C₁  = PB.axiom (srel C₁)
  weaken-qrel k C₂  = PB.axiom (srel C₂)
  weaken-qrel k C₃  = PB.axiom (srel C₃)
  weaken-qrel k C₄  = PB.axiom (srel C₄)
  weaken-qrel k C₅  = PB.axiom (srel C₅)
  weaken-qrel k C₆  = PB.axiom (srel C₆)
  weaken-qrel k C₇  = PB.axiom (srel C₇)
  weaken-qrel k C₈  = PB.axiom (srel C₈)
  weaken-qrel k C₉  = PB.axiom (srel C₉)
  weaken-qrel k C₁₀ = PB.axiom (srel C₁₀)
  weaken-qrel k C₁₁ = PB.axiom (srel C₁₁)
  weaken-qrel k C₁₂ = PB.axiom (srel C₁₂)
  weaken-qrel k C₁₃ = PB.axiom (srel C₁₃)
  weaken-qrel k C₁₄ = PB.axiom (srel C₁₄)
  weaken-qrel k C₁₅ = PB.axiom (srel C₁₅)
  weaken-qrel k C₁₆ = PB.axiom (srel C₁₆)
  weaken-qrel k C₁₇ = PB.axiom (srel C₁₇)
  weaken-qrel k C₁₈ = PB.axiom (srel C₁₈)

  weaken-ax : ∀ {n w v} k → n VRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-ax k (srel a)                  = weaken-qrel k a
  weaken-ax k (cong↑ {w = w} {v = v} a) =
    Eq.subst₂ (λ x y → _ ⊢ x ≈ y) (Eq.sym (↑-↓ᵏ w k)) (Eq.sym (↑-↓ᵏ v k))
      (lemma-cong↑ (w ↓ᵏ k) (v ↓ᵏ k) (weaken-ax k a))
  weaken-ax k (comm₁ h g)               = PB.axiom (comm₁ h (g ↧ᵏ k))
  weaken-ax k (comm₂ h g)               = PB.axiom (comm₂ h (g ↧ᵏ k))
  weaken-ax k (ω↑=ω h)                  = PB.axiom (ω↑=ω h)

------------------------------------------------------------------------
-- The congruence

weaken : ∀ {n w v} k → n ⊢ w ≈ v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
weaken k PB.refl        = PB.refl
weaken k (PB.sym e)     = PB.sym (weaken k e)
weaken k (PB.trans e f) = PB.trans (weaken k e) (weaken k f)
weaken k (PB.cong e f)  = PB.cong (weaken k e) (weaken k f)
weaken k PB.assoc       = PB.assoc
weaken k PB.left-unit   = PB.left-unit
weaken k PB.right-unit  = PB.right-unit
weaken k (PB.axiom a)   = weaken-ax k a

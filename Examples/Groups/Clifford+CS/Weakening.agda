------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation between circuits holds on the bottom wires of any wider
-- circuit
--
-- A derivation on n wires is replayed on n + k wires, the k new wires
-- idle on top: each rule of Syntactics is stated at every width above
-- its own, and the structural rules are natural in the width.  Unlike
-- Real-Clifford+CH's, whose schema (19) holds every wire of its width,
-- every rule here has at most four wires and is stated at its own, so
-- there is no bound on n.
-- With Completeness.complete≤₃ this makes completeness on up to three
-- wires available inside wider circuits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Weakening where

open import Data.Nat using (ℕ ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics

------------------------------------------------------------------------
-- Widening commutes with shifting

↑-↓ᵏ : ∀ {n} (w : Circuit n) k → (w ↑) ↓ᵏ k ≡ (w ↓ᵏ k) ↑
↑-↓ᵏ [ g ]ʷ  k = Eq.refl
↑-↓ᵏ ε       k = Eq.refl
↑-↓ᵏ (w • v) k = Eq.cong₂ _•_ (↑-↓ᵏ w k) (↑-↓ᵏ v k)

------------------------------------------------------------------------
-- The rules

private
  -- Each rule of Syntactics: the same rule at the wider width.
  weaken-srel : ∀ {n w v} k → n SRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-srel k order-I     = PB.axiom (srel order-I)
  weaken-srel k order-S     = PB.axiom (srel order-S)
  weaken-srel k order-K     = PB.axiom (srel order-K)
  weaken-srel k order-SK    = PB.axiom (srel order-SK)
  weaken-srel k order-CS    = PB.axiom (srel order-CS)
  weaken-srel k comm-CS-S₀  = PB.axiom (srel comm-CS-S₀)
  weaken-srel k comm-CS-S₁  = PB.axiom (srel comm-CS-S₁)
  weaken-srel k X-CS₀       = PB.axiom (srel X-CS₀)
  weaken-srel k X-CS₁       = PB.axiom (srel X-CS₁)
  weaken-srel k CS-K₀       = PB.axiom (srel CS-K₀)
  weaken-srel k CS-K₁       = PB.axiom (srel CS-K₁)
  weaken-srel k comm-CS↑-CS = PB.axiom (srel comm-CS↑-CS)
  weaken-srel k rel-266     = PB.axiom (srel rel-266)
  weaken-srel k rel-267     = PB.axiom (srel rel-267)
  weaken-srel k rel-268     = PB.axiom (srel rel-268)
  weaken-srel k rel-269     = PB.axiom (srel rel-269)
  weaken-srel k rel-272     = PB.axiom (srel rel-272)
  weaken-srel k cx-ccz      = PB.axiom (srel cx-ccz)
  weaken-srel k toff-ccz    = PB.axiom (srel toff-ccz)

  -- With the structural rules.
  weaken-ax : ∀ {n w v} k → n VRel, w === v → (n + k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
  weaken-ax k (srel a)                  = weaken-srel k a
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

------------------------------------------------------------------------
-- Presentations of groups
--
-- The structural commutation at any split of the wires
--
-- A circuit on the bottom k wires commutes with one on the wires above:
-- the structural rules comm₁, comm₂ and the central scalar, generator by
-- generator (the lifted ones by cong↑).  TopWeakening.low-comm is the
-- case k = 2, Idle.low₁-comm the case k = 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Low where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Place using (↑ᵏ-↑)

private
  variable
    n : ℕ

private
  lowᵍ : ∀ k (g : Gen k) (v : Circuit n) →
         (k + n) ⊢ [ g ↧ᵏ n ]ʷ • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • [ g ↧ᵏ n ]ʷ
  lowᵍ k (gate₀ h) v = PB.sym (comm-gate₀-w h (v ↑ᵏ k))
  lowᵍ {n} (suc m) (gate₁ h) v =
    Eq.subst (λ x → (suc (m + n)) ⊢ [ gate₁ h ]ʷ • x ≈ x • [ gate₁ h ]ʷ) (↑ᵏ-↑ v m)
      (PB.sym (comm-gate₁-w↑ h (v ↑ᵏ m)))
  lowᵍ {n} (suc (suc m)) (gate₂ h) v =
    Eq.subst (λ x → (suc (suc (m + n))) ⊢ [ gate₂ h ]ʷ • x ≈ x • [ gate₂ h ]ʷ)
      (Eq.trans (Eq.cong _↑ (↑ᵏ-↑ v m)) (↑ᵏ-↑ v (suc m)))
      (PB.sym (comm-gate₂-w↑↑ h (v ↑ᵏ m)))
  lowᵍ {n} (suc m) (g ↥) v =
    Eq.subst (λ x → (suc (m + n)) ⊢ [ (g ↧ᵏ n) ↥ ]ʷ • x ≈ x • [ (g ↧ᵏ n) ↥ ]ʷ) (↑ᵏ-↑ v m)
      (lemma-cong↑ ([ g ↧ᵏ n ]ʷ • (v ↑ᵏ m)) ((v ↑ᵏ m) • [ g ↧ᵏ n ]ʷ) (lowᵍ m g v))

lowᵏ : ∀ k (u : Circuit k) (v : Circuit n) → (k + n) ⊢ (u ↓ᵏ n) • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • (u ↓ᵏ n)
lowᵏ k [ g ]ʷ v = lowᵍ k g v
lowᵏ {n} k ε v = PB.trans PB.left-unit (PB.sym PB.right-unit)
lowᵏ {n} k (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • (v ↑ᵏ k)   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • (v ↑ᵏ k))   ≈⟨ back _ (lowᵏ k t v) ⟩
  (u ↓ᵏ n) • ((v ↑ᵏ k) • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • (v ↑ᵏ k)) • (t ↓ᵏ n)   ≈⟨ front _ (lowᵏ k u v) ⟩
  ((v ↑ᵏ k) • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  (v ↑ᵏ k) • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools (_VRel,_===_ (k + n))

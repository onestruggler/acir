------------------------------------------------------------------------
-- Presentations of groups
--
-- Minimal and complete rule sets, read against a semantics
--
-- A fragment's rule set on n wires (n ⊢_===_) is its axioms placed
-- anywhere on n wires, with the laws of the symmetry and the structural
-- rules: the relation whose congruence is derivability on n wires.  A
-- relation on circuits of width n is complete (_IsComplete) when it
-- derives every equation between them that the semantics validates.
-- The rule set on n wires is minimal (_IsMinimal) when each of its
-- axioms of arity n is necessary for that: without it, the others are
-- not complete on n wires (Section 5.1).  Minimality is about the rule
-- set, which says what dropping an axiom is, so _IsMinimal applies to
-- n ⊢_===_ alone: it takes an instance argument IsRuleSet Γ, which has
-- the one instance IsRuleSet (n ⊢_===_).
--
-- The semantics being sound, an independent axiom is necessary
-- (Necessity): Theorem 37's independence (Prop.Axioms.Minimal, and
-- Minimal-upto below a width) gives minimality (minimal, minimal-upto).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.MinimalComplete (Gate : ℕ → Set) where

open import Data.Nat using (_≤_)
open import Relation.Nullary.Negation using (¬_)

import Presentation.Base as PB
open import Presentation.Independence using (_∣_)
open import Examples.Independence.Prop Gate

module Rule-Set
  (_SRel,_===_ : (n : ℕ) → CRel n)
  (let open Lift-To-Prop _SRel,_===_)
  {S : ℕ → Set} (⟦_⟧ : ∀ {n} → Circuit n → S n)
  (_≋_ : ∀ {n} → S n → S n → Set)
  (sound : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → ⟦ w ⟧ ≋ ⟦ v ⟧)
  where

  open Axioms _SRel,_===_ using (Without ; Minimal ; Minimal-upto)

  ----------------------------------------------------------------------
  -- The rule set on n wires

  infix 4 _⊢_===_
  _⊢_===_ : (n : ℕ) → CRel n
  n ⊢ w === v = n VRel, w === v

  -- Γ is the rule set on n wires: the one instance.
  data IsRuleSet {n : ℕ} : CRel n → Set₁ where
    instance rule-set : IsRuleSet (n ⊢_===_)

  ----------------------------------------------------------------------
  -- Completeness and minimality

  -- Γ derives every equation between circuits of width n that the
  -- semantics validates.
  _IsComplete : ∀ {n} → CRel n → Set
  _IsComplete {n} Γ = ∀ {w v : Circuit n} → ⟦ w ⟧ ≋ ⟦ v ⟧ → PB._≈_ Γ w v

  -- Without any one of its axioms of arity n, the rule set on n wires
  -- is not complete.
  _IsMinimal : ∀ {n} (Γ : CRel n) → ⦃ IsRuleSet Γ ⦄ → Set
  _IsMinimal {n} _ ⦃ rule-set ⦄ =
    ∀ {w v : Circuit n} (ρ : n SRel, w === v) → ¬ (((n ⊢_===_) ∣ Without ρ) IsComplete)

  ----------------------------------------------------------------------
  -- From independence

  -- An independent axiom is necessary for completeness on its own
  -- wires, its own two sides being an equation the semantics validates.
  minimal : Minimal → ∀ {n} → (n ⊢_===_) IsMinimal
  minimal ind ρ complete = ind ρ (complete (sound (PB.axiom (srel (srel ρ)))))

  minimal-upto : ∀ {b} → Minimal-upto b → ∀ {n} → n ≤ b → (n ⊢_===_) IsMinimal
  minimal-upto ind n≤b ρ complete = ind ρ n≤b (complete (sound (PB.axiom (srel (srel ρ)))))

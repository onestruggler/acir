------------------------------------------------------------------------
-- Presentations of groups
--
-- Minimality read against a semantics (Section 5.1)
--
-- "Because the presentations are sound for their intended semantics,
-- an axiom derivable from the others cannot be necessary for
-- completeness.  Conversely, in any arity range where the reduced
-- presentation were still complete, soundness would force the removed
-- equation to remain derivable."  So an independent axiom of a sound
-- presentation is necessary for completeness: without it, the other
-- axioms do not derive every equation the semantics validates, its own
-- two sides being such an equation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.Necessity (Gate : ℕ → Set) where

open import Relation.Nullary.Negation using (¬_)

import Presentation.Base as PB
open import Presentation.Independence using (_∣_)
open import Examples.Independence.Prop Gate

module Fragment-Semantics
  (_SRel,_===_ : (n : ℕ) → CRel n)
  (let open Lift-To-Prop _SRel,_===_)
  {S : ℕ → Set} (⟦_⟧ : ∀ {n} → Circuit n → S n)
  (_≋_ : ∀ {n} → S n → S n → Set)
  (sound : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → ⟦ w ⟧ ≋ ⟦ v ⟧)
  where

  open Axioms _SRel,_===_

  -- The axioms other than ρ derive, at width n, every equation the
  -- semantics validates.
  Complete-without : ∀ {m} {wρ vρ : Circuit m} → m SRel, wρ === vρ → ℕ → Set
  Complete-without ρ n =
    ∀ {w v : Circuit n} → ⟦ w ⟧ ≋ ⟦ v ⟧ → PB._≈_ ((n VRel,_===_) ∣ Without ρ) w v

  -- An independent axiom is necessary for completeness on its own wires.
  necessary : ∀ {n} {w v : Circuit n} (ρ : n SRel, w === v) →
              Independent-axiom ρ → ¬ Complete-without ρ n
  necessary ρ ind complete = ind (complete (sound (PB.axiom (srel (srel ρ)))))

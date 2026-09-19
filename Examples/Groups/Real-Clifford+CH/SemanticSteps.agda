------------------------------------------------------------------------
-- Presentations of groups
--
-- Steps justified by completeness at a lower width
--
-- The paper proves its auxiliary equations on n qubits with
-- completeness on fewer qubits as a black box: "by Lemma 7.6" inside a
-- three-qubit derivation, "by Lemma D.3" inside a four-qubit one.  Such
-- a step is an equation between two circuits on k wires with the same
-- matrix; here it is one evaluation on stored tries (`Same u v`, by
-- `Eq.refl`), turned into a derivation by completeness on k wires and
-- carried to the bottom k wires of a wider circuit by Weakening, or to
-- the wires above by shifting.
--
-- The evaluation is the one Soundness uses for its relators: an
-- equality of tries checked by conversion, which takes about a second
-- per gate at width 3 — not a decision by mat-dec, whose cost explodes
-- past thirty gates.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.SemanticSteps where

open import Data.Nat using (ℕ ; _≤_) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (Same)
open import Examples.Groups.Real-Clifford+CH.Weakening using (weaken)

-- Two circuits with the same stored matrix have the same semantics.
same-sem : ∀ {k} (u v : Circuit k) → Same u v → ⟦ u ⟧ ~ ⟦ v ⟧
same-sem u v eq =
  ≐-trans (·-cong Eq.refl (⟦⟧-ix u))
    (≐-trans (≐-sym (ix-scaleM (√2^ len v) ⟦ u ⟧M))
      (≐-trans (ix-≡ eq)
        (≐-trans (ix-scaleM (√2^ len u) ⟦ v ⟧M) (·-cong Eq.refl (≐-sym (⟦⟧-ix v))))))

-- An evaluation, as a record: a lemma that takes one as a hypothesis
-- about words with a free variable must not let the conversion checker
-- unfold `Same` — it would normalise products of tries with a neutral
-- factor, which exhausts memory.  A record type is compared by its
-- parameters, the two words.
record Evaluated {k : ℕ} (u v : Circuit k) : Set where
  constructor evaluated
  field
    same : Same u v

-- Given completeness on k ≤ 4 wires.
module Below (k : ℕ) (k≤4 : k ≤ 4)
             (complete : ∀ {u v : Circuit k} → ⟦ u ⟧ ~ ⟦ v ⟧ → k ⊢ u ≈ v) where

  -- At width k.
  by-sem₀ : (u v : Circuit k) → Same u v → k ⊢ u ≈ v
  by-sem₀ u v eq = complete (same-sem u v eq)

  -- On the bottom k wires of a wider circuit.
  by-sem : (u v : Circuit k) → Same u v → ∀ {n} → (k +ℕ n) ⊢ u ↓ᵏ n ≈ v ↓ᵏ n
  by-sem u v eq {n} = weaken n k≤4 (by-sem₀ u v eq)

  -- One wire up.
  by-sem↑ : (u v : Circuit k) → Same u v → ∀ {n} → (₁₊ (k +ℕ n)) ⊢ (u ↓ᵏ n) ↑ ≈ (v ↓ᵏ n) ↑
  by-sem↑ u v eq {n} = lemma-cong↑ (u ↓ᵏ n) (v ↓ᵏ n) (by-sem u v eq)

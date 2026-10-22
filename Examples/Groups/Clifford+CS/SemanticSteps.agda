------------------------------------------------------------------------
-- Presentations of groups
--
-- Steps justified by completeness at a lower width
--
-- Clément proves his auxiliary equations on n qubits with completeness
-- on fewer qubits as a black box, and so does the development from
-- four wires on here: a step is an equation between two circuits on
-- k ≤ 3 wires with the same matrix, decided by one boolean on their
-- row-operation readings (`Same u v`, by `Eq.refl`; MacroEval's, which
-- charges γ to K alone and applies the shortcuts whole), turned into a
-- derivation by completeness on k wires (Completeness.complete≤₃, the
-- parameter of `Below`) and
-- carried to the bottom k wires of a wider circuit by Weakening, or to
-- the wires above by shifting.  This is Real-Clifford+CH.SemanticSteps
-- for the Clifford+CS gates, where the width bound is three rather
-- than four and the scale is γ rather than √2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.SemanticSteps where

open import Data.Nat using (ℕ ; _≤_) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Clifford+CS.MacroEval using (SameF ; sameF-sem)
open import Examples.Groups.Clifford+CS.Weakening using (weaken)

------------------------------------------------------------------------
-- Two circuits with the same matrix

-- Decided by one boolean on the fast row-operation readings, each scaled
-- by the other's power of γ (MacroEval: the readings charge γ to K alone,
-- as FastEval's do, and apply a Swap, CNOT, Toffoli, CZ, CCZ or
-- controlled K as one row operation; five times faster than FastEval's
-- on the windows of Four/ and Five/).
Same : ∀ {k} → Circuit k → Circuit k → Set
Same u v = SameF u v

-- Hence the same semantics.
same-sem : ∀ {k} (u v : Circuit k) → Same u v → ⟦ u ⟧ ~ ⟦ v ⟧
same-sem = sameF-sem

same-≡ : ∀ {k} (u v : Circuit k) → Same u v →
         scaleM (γ^ len v) ⟦ u ⟧M ≡ scaleM (γ^ len u) ⟦ v ⟧M
same-≡ u v e =
  mat-ext (≐-trans (ix-scaleM (γ^ len v) ⟦ u ⟧M)
    (≐-trans (·-cong Eq.refl (≐-sym (⟦⟧-ix u)))
      (≐-trans (same-sem u v e)
        (≐-trans (·-cong Eq.refl (⟦⟧-ix v)) (≐-sym (ix-scaleM (γ^ len u) ⟦ v ⟧M))))))

-- An evaluation, as a record: a lemma that takes one as a hypothesis
-- about words with a free variable must not let the conversion checker
-- unfold `Same` — it would normalise products of tries with a neutral
-- factor, which exhausts memory.  A record type is compared by its
-- parameters, the two words.
record Evaluated {k : ℕ} (u v : Circuit k) : Set where
  constructor evaluated
  field
    same : Same u v

------------------------------------------------------------------------
-- Steps, given completeness at the width

module Below (k : ℕ) (complete : ∀ {u v : Circuit k} → ⟦ u ⟧ ~ ⟦ v ⟧ → k ⊢ u ≈ v) where

  -- At width k.
  by-sem₀ : (u v : Circuit k) → Same u v → k ⊢ u ≈ v
  by-sem₀ u v eq = complete (same-sem u v eq)

  -- On the bottom k wires of a wider circuit.
  by-sem : (u v : Circuit k) → Same u v → ∀ {n} → (k +ℕ n) ⊢ u ↓ᵏ n ≈ v ↓ᵏ n
  by-sem u v eq {n} = weaken n (by-sem₀ u v eq)

  -- One wire up.
  by-sem↑ : (u v : Circuit k) → Same u v → ∀ {n} → (₁₊ (k +ℕ n)) ⊢ (u ↓ᵏ n) ↑ ≈ (v ↓ᵏ n) ↑
  by-sem↑ u v eq {n} = lemma-cong↑ (u ↓ᵏ n) (v ↓ᵏ n) (by-sem u v eq)

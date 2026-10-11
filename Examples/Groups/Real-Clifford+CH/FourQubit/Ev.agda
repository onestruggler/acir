------------------------------------------------------------------------
-- Presentations of groups
--
-- Using a stored evaluation
--
-- An evaluation kept in another module (`Evaluated u v`, minutes of
-- conversion checking) must be used with its words read off its type,
-- not typed again: two modules that open the parameterised Blocks hold
-- different copies of L₀, U₀, O₀, so a word typed again is only
-- definitionally the stored one, and the conversion checker settles
-- that by unfolding `Same` — evaluating both sides once more.  These
-- versions of the block lemmas take the record with its words implicit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Ev
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)

open import Notations using (₄₊)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃

private
  variable
    n : ℕ

L₃-ev : ∀ {u v : Circuit 3} → Evaluated u v → (₄₊ n) ⊢ L₃ u ≈ L₃ v
L₃-ev {u = u} {v} e = L₃-sem u v (Evaluated.same e)

U₃-ev : ∀ {u v : Circuit 3} → Evaluated u v → (₄₊ n) ⊢ U₃ u ≈ U₃ v
U₃-ev {u = u} {v} e = U₃-sem u v (Evaluated.same e)

O₃-ev : ∀ {u v : Circuit 3} → Evaluated u v → (₄₊ n) ⊢ O₃ u ≈ O₃ v
O₃-ev {u = u} {v} e = O₃-sem u v (Evaluated.same e)

M₃-ev : ∀ {u v : Circuit 3} → Evaluated u v → (₄₊ n) ⊢ M₃ u ≈ M₃ v
M₃-ev {u = u} {v} e = M₃-sem u v (Evaluated.same e)

L₃-comm-ev : ∀ {u v : Circuit 3} → Evaluated (u • v) (v • u) → (₄₊ n) ⊢ L₃ u • L₃ v ≈ L₃ v • L₃ u
L₃-comm-ev {u = u} {v} e = L₃-comm u v (Evaluated.same e)

U₃-comm-ev : ∀ {u v : Circuit 3} → Evaluated (u • v) (v • u) → (₄₊ n) ⊢ U₃ u • U₃ v ≈ U₃ v • U₃ u
U₃-comm-ev {u = u} {v} e = U₃-comm u v (Evaluated.same e)

O₃-comm-ev : ∀ {u v : Circuit 3} → Evaluated (u • v) (v • u) → (₄₊ n) ⊢ O₃ u • O₃ v ≈ O₃ v • O₃ u
O₃-comm-ev {u = u} {v} e = O₃-comm u v (Evaluated.same e)

M₃-comm-ev : ∀ {u v : Circuit 3} → Evaluated (u • v) (v • u) → (₄₊ n) ⊢ M₃ u • M₃ v ≈ M₃ v • M₃ u
M₃-comm-ev {u = u} {v} e = M₃-comm u v (Evaluated.same e)

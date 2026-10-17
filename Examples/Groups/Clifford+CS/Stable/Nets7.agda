------------------------------------------------------------------------
-- Presentations of groups
--
-- Swap networks and placements on six and seven wires, and the two
-- S-boxes of Stable.Base7
--
-- Kept apart from Stable.Base7, whose module parameters (completeness
-- on five and six wires) they do not need, so that Stable.Windows6 can
-- state and prove the windows' equalities of semantics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Nets7 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-2-43-1)

------------------------------------------------------------------------
-- Networks

-- The swap of the wires p, p + 1.
sw₇ : ℕ → Word (S.Gen 7)
sw₇ 0 = [ S.gate₂ S.σ-gate ]ʷ
sw₇ 1 = [ S.gate₂ S.σ-gate S.↥ ]ʷ
sw₇ 2 = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ
sw₇ 3 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ ]ʷ
sw₇ 4 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ S.↥ ]ʷ
sw₇ 5 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ S.↥ S.↥ ]ʷ
sw₇ _ = ε

sw₆ : ℕ → Word (S.Gen 6)
sw₆ 0 = [ S.gate₂ S.σ-gate ]ʷ
sw₆ 1 = [ S.gate₂ S.σ-gate S.↥ ]ʷ
sw₆ 2 = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ
sw₆ 3 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ ]ʷ
sw₆ 4 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ S.↥ ]ʷ
sw₆ _ = ε

-- A network from its swaps, in time order.
ns₇ : List ℕ → Word (S.Gen 7)
ns₇ []       = ε
ns₇ (p ∷ ps) = sw₇ p • ns₇ ps

ns₆ : List ℕ → Word (S.Gen 6)
ns₆ []       = ε
ns₆ (p ∷ ps) = sw₆ p • ns₆ ps

------------------------------------------------------------------------
-- Placements and windows

-- A five-wire circuit placed on seven wires, and on six.
P₇ : Word (S.Gen 7) → Circuit 5 → Circuit 7
P₇ s u = pl s (u ↓ᵏ 2)

P₆ : Word (S.Gen 6) → Circuit 5 → Circuit 6
P₆ s u = pl s (u ↓ᵏ 1)

------------------------------------------------------------------------
-- The two S-boxes

Σ₀ Σ₂ : Circuit 5
Σ₀ = b-Sb2-0-41-3
Σ₂ = b-Sb0-2-43-1

-- The four windows' equalities of semantics on six wires.  Deciding them
-- by evaluation exhausts 8 GB (the S-boxes placed on six wires); each
-- is a controlled CS conjugated by swaps of wires the control does not
-- see, which a semantic lemma will give (scratchpad/five-qubit-plan.md).
record Windows₆ : Set where
  field
    w₁ : ⟦ P₆ (ns₆ (4 ∷ [])) Σ₀ ⟧ ~ ⟦ P₆ (ns₆ (3 ∷ 4 ∷ [])) Σ₀ ⟧
    w₂ : ⟦ P₆ (ns₆ (3 ∷ 4 ∷ [])) Σ₀ ⟧ ~ ⟦ P₆ (ns₆ (2 ∷ 3 ∷ 4 ∷ [])) Σ₀ ⟧
    w₃ : ⟦ P₆ (ns₆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂ ⟧ ~ ⟦ P₆ (ns₆ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂ ⟧
    w₄ : ⟦ P₆ (ns₆ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂ ⟧ ~ ⟦ P₆ (ns₆ (2 ∷ 3 ∷ 4 ∷ [])) Σ₂ ⟧


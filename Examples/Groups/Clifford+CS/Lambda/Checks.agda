------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor: the evaluations its semantics rests on
--
-- Each base letter of Lambda, at the width where it is a closed word,
-- denotes its controlled gate: `check` decides ⟦ w ⟧ ~ (l , T) by one
-- boolean on the row-operation reading (Evaluation), as SemanticSteps
-- decides `Same`.  The three S-boxes are the five-wire evaluations;
-- the rest are on one or two wires.  Kept apart so that the
-- evaluations are done once.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.Checks where

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; len)
open import Examples.Groups.Clifford+CS.MacroEval using (ChkOp ; F-op)
open import Examples.Groups.Clifford+CS.MultiControlled using (CK₁₀)
open import Examples.Groups.Clifford+CS.Five.Letters
  using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)

------------------------------------------------------------------------
-- Deciding a circuit's semantics against an operator

check : ∀ {k} (w : Circuit k) (l : ℕ) (T : Op k) → ChkOp w l T → ⟦ w ⟧ ~ (l , T)
check = F-op

------------------------------------------------------------------------
-- One and two wires

-- S is i controlled by its wire.
S-ctrl : ⟦ S {0} ⟧ ~ ctrl (1 , scal γⅈ)
S-ctrl = check S 1 (blk (scal (γ^ 1)) (scal γⅈ)) Eq.refl

-- CS is S on wire 0 controlled by wire 1.
CS-ctrl : ⟦ CS {0} ⟧ ~ ctrl (1 , emb {1} {0} sM)
CS-ctrl = check CS 1 (blk (scal (γ^ 1)) (emb sM)) Eq.refl

-- CK₁₀ is K on wire 0 controlled by wire 1.
CK-ctrl : ⟦ CK₁₀ {0} ⟧ ~ ctrl (1 , emb {1} {0} kM)
CK-ctrl = check CK₁₀ 1 (blk (scal (γ^ 1)) (emb kM)) Eq.refl

-- The swap and X are permutations.
Swap-perm : ⟦ Swap {0} ⟧ ~ (0 , permOp swapL)
Swap-perm = check Swap 0 (permOp swapL) Eq.refl

X-perm : ⟦ X {0} ⟧ ~ (0 , permOp flipL)
X-perm = check X 0 (permOp flipL) Eq.refl

------------------------------------------------------------------------
-- Five wires: the doubly controlled S, CS of a pair of the bottom four
-- wires controlled by wire 4

-- Σ(0; 4, 1 | 2, 3).
Σ₀₁ : ⟦ b-Sb2-0-41-3 ⟧ ~ ctrl (1 , emb {2} {2} csM)
Σ₀₁ = check b-Sb2-0-41-3 1 (blk (scal (γ^ 1)) (emb csM)) Eq.refl

-- Σ(1; 4, 2 | 0, 3).
Σ₁₂ : ⟦ b-Sb0-1-42-3 ⟧ ~ ctrl (1 , up (emb {2} {1} csM))
Σ₁₂ = check b-Sb0-1-42-3 1 (blk (scal (γ^ 1)) (up (emb csM))) Eq.refl

-- Σ(2; 4, 3 | 0, 1).
Σ₂₃ : ⟦ b-Sb0-2-43-1 ⟧ ~ ctrl (1 , up (up (emb {2} {0} csM)))
Σ₂₃ = check b-Sb0-2-43-1 1 (blk (scal (γ^ 1)) (up (up (emb csM)))) Eq.refl

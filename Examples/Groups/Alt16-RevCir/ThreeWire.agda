------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules (1)–(7) are complete on one, two and three wires
--
-- Two circuits over this folder's gates on at most three wires that
-- are the same function on states are equal by the rules of Theory:
-- Propositions B.1–B.3 of "Block Normal Forms and Certified Equations
-- for Four-Bit Reversible Circuits", which
-- Examples.Groups.XCXCCX-4bit proves (Width1, Width2, Width3: the edge
-- Toffolis along the Gray code satisfy the Coxeter relations of S₈),
-- carried to this folder's gates by Relabel.  On three wires only the
-- rules (1)–(6) and the laws of the swap take part: rule (7) lives on
-- four.
--
-- This is what a step on three wires of a four-wire derivation rests
-- on.  on₀₁₂, …, on₀₂₃ place a three-wire circuit on three of the four
-- wires, the bottom and the top three directly and the other two
-- triples between swaps, and step₀₁₂, …, step₀₂₃ are completeness for
-- circuits so placed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Alt16-RevCir.ThreeWire where

open import Word.Base using (_•_)

import Presentation.Base as PB

import Examples.Groups.XCXCCX-4bit.Width1 as W1
import Examples.Groups.XCXCCX-4bit.Width2 as W2
import Examples.Groups.XCXCCX-4bit.Width3 as W3

open import Examples.Groups.Alt16-RevCir.Relabel using (module Transfer)
open import Examples.Groups.Alt16-RevCir.Semantics using (⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using (Circuit ; _↑ ; _↓ᵏ_ ; Ex₀ ; Ex₂)
open import Examples.Groups.Alt16-RevCir.Theory using (module T)

------------------------------------------------------------------------
-- Completeness on one, two and three wires

complete₁ : {w v : Circuit 1} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 1 T.⊢ w ≈ v
complete₁ = Transfer.complete (λ {u} {v} → W1.complete₁ {u} {v})

complete₂ : {w v : Circuit 2} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 2 T.⊢ w ≈ v
complete₂ = Transfer.complete (λ {u} {v} → W2.complete₂ {u} {v})

complete₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 3 T.⊢ w ≈ v
complete₃ = Transfer.complete (λ {u} {v} → W3.complete₃ {u} {v})

------------------------------------------------------------------------
-- A three-wire circuit on three of the four wires

-- The circuit on the wires named, in order: the bottom three and the
-- top three directly, the other two triples between swaps.
on₀₁₂ on₁₂₃ on₀₁₃ on₀₂₃ : Circuit 3 → Circuit 4
on₀₁₂ w = w ↓ᵏ 1
on₁₂₃ w = w ↑
on₀₁₃ w = Ex₂ • on₀₁₂ w • Ex₂
on₀₂₃ w = Ex₀ • on₁₂₃ w • Ex₀

------------------------------------------------------------------------
-- A three-wire step on four wires

-- Two three-wire circuits with the same function, on the same three of
-- the four wires, are equal by the rules.
step₀₁₂ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 T.⊢ on₀₁₂ w ≈ on₀₁₂ v
step₀₁₂ e = T.pad₃ (complete₃ e) 1

step₁₂₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 T.⊢ on₁₂₃ w ≈ on₁₂₃ v
step₁₂₃ e = T.lemma-cong↑ _ _ (complete₃ e)

step₀₁₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 T.⊢ on₀₁₃ w ≈ on₀₁₃ v
step₀₁₃ e = PB.cong PB.refl (PB.cong (step₀₁₂ e) PB.refl)

step₀₂₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 T.⊢ on₀₂₃ w ≈ on₀₂₃ v
step₀₂₃ e = PB.cong PB.refl (PB.cong (step₁₂₃ e) PB.refl)

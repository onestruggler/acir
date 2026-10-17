------------------------------------------------------------------------
-- Presentations of groups
--
-- The S-box does not see the order of its control and its second wire
--
-- Σ(x; t, y | u, A), the CS of x and y controlled by t, is the doubly
-- controlled S on x, t, y: exchanging t and y (the wires 4 and 1 of
-- the canonical letter b-Sb2-0-41-3, by the network ρ) leaves it
-- unchanged.  On five wires that is one evaluation (77 s, 4.9 GB) and
-- completeness there (`sb`); on any wider circuit the same with idle
-- wires on top (`sbW`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.SboxSym where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)

open import Notations using (₄₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _↓ᵏ_)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (top-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

-- The exchange of the wires 1 and 4, by adjacent swaps.
ρ : ∀ {k} → Word (S.Gen (suc (₄₊ k)))
ρ = (S.σ S.↑) • (S.σ S.↑ S.↑) • (S.σ S.↑ S.↑ S.↑) • (S.σ S.↑ S.↑) • (S.σ S.↑)

private
  same : Same b-Sb2-0-41-3 (pl ρ b-Sb2-0-41-3)
  same = Eq.refl

sb : Completeᵧ 5 → 5 ⊢ᵧ b-Sb2-0-41-3 ≈ pl ρ b-Sb2-0-41-3
sb c₅ = c₅ (same-sem b-Sb2-0-41-3 (pl ρ b-Sb2-0-41-3) same)

sbW : Completeᵧ 5 → ∀ k → (suc (₄₊ k)) ⊢ᵧ b-Sb2-0-41-3 ↓ᵏ k ≈ pl ρ (b-Sb2-0-41-3 ↓ᵏ k)
sbW c₅ zero    = sb c₅
sbW c₅ (suc k) = top-congᵧ (sbW c₅ k)

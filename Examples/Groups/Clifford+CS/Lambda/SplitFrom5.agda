------------------------------------------------------------------------
-- Presentations of groups
--
-- Lambda.Split's three five-wire equations from completeness on five
--
-- From six wires on, the CS equations of `Lambda.Split.F5` follow from
-- completeness on five wires, each by one evaluation.  In a module of
-- its own, since the three evaluations were most of Split's time and
-- nothing that imports Split needs them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.SplitFrom5 where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (_•_)

open import Notations using (₄)

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-sem)
open import Examples.Groups.Clifford+CS.Lambda using (Xᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Split using (F5)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)

F5-from : (∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ₓ u ≈ v) → F5
F5-from c₅ = record
  { cs₀₁ = c₅ (same-sem CS ((Xᵗ ₄ • b-Sb2-0-41-3 • Xᵗ ₄) • b-Sb2-0-41-3) Eq.refl)
  ; cs₁₂ = c₅ (same-sem (CS ↑) ((Xᵗ ₄ • b-Sb0-1-42-3 • Xᵗ ₄) • b-Sb0-1-42-3) Eq.refl)
  ; cs₂₃ = c₅ (same-sem (CS ↑ ↑) ((Xᵗ ₄ • b-Sb0-2-43-1 • Xᵗ ₄) • b-Sb0-2-43-1) Eq.refl)
  }

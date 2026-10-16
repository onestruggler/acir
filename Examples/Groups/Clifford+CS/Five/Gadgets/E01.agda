------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire facts about the gadgets (pp-cx₀, pp-cx₁, pp-cx₂, pp-sw₁, pp-sw₂, rot-cx₀)
--
-- Each is one evaluation, turned into a derivation by completeness on
-- four wires; a module holds a few, since Agda frees the memory of an
-- evaluation only when its module is done.  Written by
-- `scratchpad/five/gadgets5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Five.Gadgets.E01 (c4 : Complete 4) where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Presentation.GroupLike using (module Group-Lemmas)
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)
open import Examples.Groups.Clifford+CS.Five.Gadgets.Words

open Group-Lemmas (_VRel,_===_ 4) grouplike using (_⁻¹)

private
  by : (u v : Circuit 4) → Same u v → 4 ⊢ u ≈ v
  by u v e = c4 (same-sem u v e)

pp-cx₀ : 4 ⊢ (CX₁₀) • G-pp ≈ G-pp • (CX₁₀)
pp-cx₀ = by ((CX₁₀) • G-pp) (G-pp • (CX₁₀)) Eq.refl

pp-cx₁ : 4 ⊢ (CX₁₀ ↑) • G-pp ≈ G-pp • (CX₁₀ ↑)
pp-cx₁ = by ((CX₁₀ ↑) • G-pp) (G-pp • (CX₁₀ ↑)) Eq.refl

pp-cx₂ : 4 ⊢ (CX₁₀ ↑ ↑) • G-pp ≈ G-pp • (CX₁₀ ↑ ↑)
pp-cx₂ = by ((CX₁₀ ↑ ↑) • G-pp) (G-pp • (CX₁₀ ↑ ↑)) Eq.refl

pp-sw₁ : 4 ⊢ (Swap ↑) • G-pp ≈ G-pp • (Swap ↑)
pp-sw₁ = by ((Swap ↑) • G-pp) (G-pp • (Swap ↑)) Eq.refl

pp-sw₂ : 4 ⊢ (Swap ↑ ↑) • G-pp ≈ G-pp • (Swap ↑ ↑)
pp-sw₂ = by ((Swap ↑ ↑) • G-pp) (G-pp • (Swap ↑ ↑)) Eq.refl

rot-cx₀ : 4 ⊢ (CX₁₀) • G-rot ≈ G-rot • (CX₁₀)
rot-cx₀ = by ((CX₁₀) • G-rot) (G-rot • (CX₁₀)) Eq.refl

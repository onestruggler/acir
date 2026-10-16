------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire facts about the gadgets (dec-c)
--
-- Each is one evaluation, turned into a derivation by completeness on
-- four wires; a module holds a few, since Agda frees the memory of an
-- evaluation only when its module is done.  Written by
-- `scratchpad/five/gadgets5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Five.Gadgets.E14 (c4 : Complete 4) where

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

dec-c : 4 ⊢ G-ki • G-rot ≈ G-pp • G-ki
dec-c = by (G-ki • G-rot) (G-pp • G-ki) Eq.refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Re-bracketings of four-wire circuits, decided by one boolean
--
-- `by-assoc Eq.refl` makes the conversion checker flatten both words
-- and compare the lists, slowly and in much memory on words of
-- hundreds of gates (the gadget spellings of Four/Facts).
-- `by-flat Eq.refl` compares the flattened generators' codes with one
-- boolean (Four.Reflect.eqLG), evaluated with sharing, as Five.Flat.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Flat where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _VRel,_===_)
open import Examples.Groups.Clifford+CS.Four.Chain using (_≈_ ; by-assoc)
open import Examples.Groups.Clifford+CS.Four.Reflect using (eqLG ; eqLG-sound)

open Assoc (_VRel,_===_ 4) using (to-list)

by-flat : ∀ {w v : Circuit 4} → eqLG (to-list w) (to-list v) ≡ true → w ≈ v
by-flat {w} {v} e = by-assoc (eqLG-sound (to-list w) (to-list v) e)

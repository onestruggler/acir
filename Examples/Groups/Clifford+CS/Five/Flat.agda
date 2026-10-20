------------------------------------------------------------------------
-- Presentations of groups
--
-- Re-bracketings of five-wire circuits, decided by one boolean
--
-- `by-assoc Eq.refl` makes the conversion checker flatten both words
-- and compare the lists; on λ¹-lifted rules, words of hundreds of
-- gates, that took Five/F1 146 s and 7.4 GB.  `by-flat Eq.refl`
-- compares the flattened generators' codes with one boolean
-- (Five.Reflect.eqLG), evaluated with sharing: F1 29 s, 5.4 GB.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Flat where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Five.Rules using (_XVRel,_===_)
open import Examples.Groups.Clifford+CS.Five.Chain using (_≈_ ; by-assoc)
open import Examples.Groups.Clifford+CS.Five.Reflect using (eqLG ; eqLG-sound)

open Assoc (_XVRel,_===_ 5) using (to-list)

by-flat : ∀ {w v : Circuit 5} → eqLG (to-list w) (to-list v) ≡ true → w ≈ v
by-flat {w} {v} e = by-assoc (eqLG-sound (to-list w) (to-list v) e)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex/CZ lemmas over the two rewrite systems (Selinger step 2).
--
-- This module is the directory's entry point and re-exports the two
-- parts it was split into; importers see exactly the names they always
-- did.  The split is by rewrite engine: Powers carries the order and
-- commutation table, Swap the swap system built on it.  See either
-- file's header for why they are apart.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Fin using (toℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality


module Examples.Groups.Symplectic.Lemmas.Ex-Sym3n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n.Powers p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n.Swap   p-2 p-prime public

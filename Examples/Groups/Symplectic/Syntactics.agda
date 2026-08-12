------------------------------------------------------------------------
-- Presentations of groups
--
-- The plain qupit-Clifford (symplectic) presentation.
--
-- This module is the directory's entry point and re-exports the
-- three parts it was split into; importers see exactly the names
-- they always did.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality

open import Notations
import Circuit.Base

module Examples.Groups.Symplectic.Syntactics (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Examples.Groups.Symplectic.Syntactics.Gates p-2 p-prime public
open import Examples.Groups.Symplectic.Syntactics.Derived p-2 p-prime public
open import Examples.Groups.Symplectic.Syntactics.Duality p-2 p-prime public

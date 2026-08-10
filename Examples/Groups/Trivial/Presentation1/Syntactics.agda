------------------------------------------------------------------------
-- Presentations of groups
--
-- First presentation of the trivial group, syntax: ⟨ ⊥ ∣ ⟩.
--
-- No generators, hence no axioms are needed.  The second presentation,
-- over an arbitrary alphabet, is Presentation2.Syntactics; both are
-- trivial for the same reason, recorded here as gen≈ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1.Syntactics where

open import Data.Empty using (⊥)

open import Presentation.Construct.Base using (EmptyRel)
open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

------------------------------------------------------------------------
-- Alphabet and relation

X : Set
X = ⊥

pres : WRel X
pres = EmptyRel

open PB pres using (_≈_)

------------------------------------------------------------------------
-- Every generator collapses

-- Vacuously: the alphabet ⊥ has no generators.  This is the single
-- hypothesis the whole development runs on -- see
-- Examples.Groups.Trivial.Normalization.
gen≈ε : ∀ (x : X) → [ x ]ʷ ≈ ε
gen≈ε ()

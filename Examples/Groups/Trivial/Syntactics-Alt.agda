------------------------------------------------------------------------
-- Presentations of groups
--
-- The trivial group via the universal relation:
-- ⟨ A ∣ w = ε for every word w ⟩.
--
-- An arbitrary alphabet, with the coarsest relation TrivialRel killing
-- every generator.  Where Syntactics has no generators to collapse,
-- here each one is collapsed by an axiom; everything downstream is
-- shared, since both supply the same gen≈ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Syntactics-Alt (A : Set) where

open import Presentation.Construct.Base using (TrivialRel ; ≈ε)
open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

------------------------------------------------------------------------
-- Alphabet and relation

X : Set
X = A

pres : WRel X
pres = TrivialRel

open PB pres using (_≈_)

------------------------------------------------------------------------
-- Every generator collapses

-- Each generator is killed by an axiom.
gen≈ε : ∀ (x : X) → [ x ]ʷ ≈ ε
gen≈ε x = _≈_.axiom ≈ε

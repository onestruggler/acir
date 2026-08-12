------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ ⊥ ∣ ⟩ presents the trivial group.
--
-- The first presentation of the trivial group: no generators, hence no
-- axioms.  Everything between the syntax and the theorem is generic --
-- the collapse argument, the normal form, its uniqueness and the
-- interpretation are all proved once in
-- Examples.Groups.Trivial.{Normalization,UniqueNormalForm,Interpretation}
-- and instantiated here at the single hypothesis gen≈ε.  What is added
-- below is the assembly and the surjectivity of the interpretation.
--
-- The second presentation, over an arbitrary alphabet, is
-- Examples.Groups.Trivial.Presentation2; that the two present
-- isomorphic monoids is
-- Examples.Groups.Trivial.Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1 where

open import Algebra.Bundles using (Group)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Presentation.Construct.Base using (EmptyRel)
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

import Examples.Groups.Trivial.Interpretation as GenericI
import Examples.Groups.Trivial.Normalization as GenericN
import Examples.Groups.Trivial.UniqueNormalForm as GenericU

open import Examples.Groups.Trivial.Semantics using (gp) public

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
-- hypothesis the whole development runs on.
gen≈ε : ∀ (x : X) → [ x ]ʷ ≈ ε
gen≈ε ()

------------------------------------------------------------------------
-- The generic development, instantiated here
--
-- Nothing is proved in this section: the three generic modules are
-- applied to gen≈ε and their results re-exported unchanged.  The normal
-- form is part of this module's interface -- clients that need the
-- trivial group as a base case take it from here
-- (Presentation.Construct.Properties.NDirectProduct does, at width 0).

private module I = GenericI pres gen≈ε

open I public using (⟦_⟧₀ ; grouplike)

open GenericN pres gen≈ε public using (w≈ε ; nf ; nfp ; nfp')

open GenericU pres gen≈ε public using (unfp)

------------------------------------------------------------------------
-- The presentation theorem

subpresentation : pres IsSubPresentationOf gp
subpresentation =
  I.GS.GetSubPresentation.groupSubPres I.fʷ-cong-ax grouplike nfp' unfp

presentation : pres IsPresentationOf gp
presentation = isPresentationOf subpresentation claim
  where
  claim : Surjective _≈_ (Group._≈_ gp) I.GS.⟦_⟧
  claim y = ε , λ _ → _

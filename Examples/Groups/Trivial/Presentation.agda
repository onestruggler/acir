------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ ⊥ ∣ ⟩ presents the trivial group.
--
-- The shared machinery instantiated at the empty alphabet.  The
-- alternative presentation, over an arbitrary alphabet, is
-- Presentation-Alt; that the two present isomorphic monoids is
-- Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Word.Base using (ε)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)

import Presentation.Base as PB

open import Examples.Groups.Trivial.Semantics using (gp) public
open import Examples.Groups.Trivial.Syntactics using (X ; pres ; gen≈ε) public

import Examples.Groups.Trivial.Interpretation as Intp
import Examples.Groups.Trivial.Normalization as Nrm
import Examples.Groups.Trivial.UniqueNormalForm as UNF

private
  module I = Intp pres gen≈ε

-- The normal form is part of this module's interface: clients that need
-- the trivial group as a base case take it from here
-- (Presentation.Construct.Properties.NDirectProduct does, at width 0).
open Nrm pres gen≈ε public using (w≈ε ; nf ; nfp ; nfp')
open I public using (⟦_⟧₀ ; grouplike)
open UNF pres gen≈ε public using (unfp)

open PB pres using (_≈_)

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

------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ A ∣ w = ε for every word w ⟩ presents the trivial group.
--
-- The same shared machinery as Presentation, instantiated at an
-- arbitrary alphabet instead of the empty one.  Only the syntactic
-- input differs: there gen≈ε holds vacuously, here by an axiom.  That
-- the two present isomorphic monoids is Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation-Alt (A : Set) where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Word.Base using (ε)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)

import Presentation.Base as PB

open import Examples.Groups.Trivial.Semantics using (gp) public
open import Examples.Groups.Trivial.Syntactics-Alt A
  using (X ; pres ; gen≈ε) public

import Examples.Groups.Trivial.Interpretation as Intp
import Examples.Groups.Trivial.Normalization as Nrm
import Examples.Groups.Trivial.UniqueNormalForm as UNF

private
  module I = Intp pres gen≈ε

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

------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ ⊥ ∣ ⟩ presents the trivial group.
--
-- The presentation theorem for the first presentation.  Everything it
-- consumes was proved generically and instantiated by the sibling
-- modules of this directory; what is added here is the assembly and the
-- surjectivity of the interpretation.
--
-- The second presentation, over an arbitrary alphabet, is
-- Presentation2.Presentation; that the two present isomorphic monoids
-- is Examples.Groups.Trivial.Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation1.Presentation where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Word.Base using (ε)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)

import Presentation.Base as PB

open import Examples.Groups.Trivial.Semantics using (gp) public
open import Examples.Groups.Trivial.Presentation1.Syntactics
  using (X ; pres ; gen≈ε) public

import Examples.Groups.Trivial.Presentation1.Interpretation as I

-- The normal form is part of this module's interface: clients that need
-- the trivial group as a base case take it from here
-- (Presentation.Construct.Properties.NDirectProduct does, at width 0).
open import Examples.Groups.Trivial.Presentation1.Normalization public
  using (w≈ε ; nf ; nfp ; nfp')
open import Examples.Groups.Trivial.Presentation1.UniqueNormalForm public
  using (unfp)

open I public using (⟦_⟧₀ ; grouplike)

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

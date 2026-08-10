------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ A ∣ w = ε for every word w ⟩ presents the trivial group.
--
-- The presentation theorem for the second presentation.  It is the same
-- assembly as Presentation1.Presentation, over an arbitrary alphabet
-- instead of the empty one; only the syntactic input differs, gen≈ε
-- holding there vacuously and here by an axiom.
--
-- That the two present isomorphic monoids is
-- Examples.Groups.Trivial.Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation2.Presentation (A : Set) where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Word.Base using (ε)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)

import Presentation.Base as PB

-- gp is re-exported, not abstracted over A: the target group is the
-- same terminal group whatever the alphabet, so this is `gp`, never
-- `gp A`.  Contrast `presentation` below, which does take A.
open import Examples.Groups.Trivial.Semantics using (gp) public
open import Examples.Groups.Trivial.Presentation2.Syntactics A
  using (X ; pres ; gen≈ε) public

import Examples.Groups.Trivial.Presentation2.Interpretation A as I

open import Examples.Groups.Trivial.Presentation2.Normalization A public
  using (w≈ε ; nf ; nfp ; nfp')
open import Examples.Groups.Trivial.Presentation2.UniqueNormalForm A public
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

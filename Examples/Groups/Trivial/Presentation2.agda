------------------------------------------------------------------------
-- Presentations of groups
--
-- ⟨ A ∣ w = ε for every word w ⟩ presents the trivial group.
--
-- The second presentation of the trivial group: an arbitrary alphabet
-- with the coarsest relation, TrivialRel, killing every generator.
-- Where Presentation1 has no generators to collapse, here each one is
-- collapsed by an axiom; everything downstream is shared, since both
-- supply the same gen≈ε and the collapse argument, the normal form, its
-- uniqueness and the interpretation are all proved generically in
-- Examples.Groups.Trivial.{Normalization,UniqueNormalForm,Interpretation}.
--
-- That the two presentations present isomorphic monoids is
-- Examples.Groups.Trivial.Presentation-Equivalence.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation2 (A : Set) where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_)
open import Function.Definitions using (Surjective)
open import Presentation.Construct.Base using (TrivialRel ; ≈ε)
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

import Examples.Groups.Trivial.Interpretation as GenericI
import Examples.Groups.Trivial.Normalization as GenericN
import Examples.Groups.Trivial.UniqueNormalForm as GenericU

-- gp is re-exported, not abstracted over A: the target group is the
-- same terminal group whatever the alphabet, so this is `gp`, never
-- `gp A`.  Contrast `presentation` below, which does take A.
open import Examples.Groups.Trivial.Semantics using (gp) public

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

------------------------------------------------------------------------
-- The generic development, instantiated here
--
-- Nothing is proved in this section: the three generic modules are
-- applied to gen≈ε and their results re-exported unchanged.

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

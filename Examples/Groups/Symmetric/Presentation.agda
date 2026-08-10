------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuit presentation of Sₙ presents the permutation group.
--
-- The assembly step: everything it consumes was proved elsewhere, and
-- the two stages are worth keeping apart.
--
--   subpresentation  needs only soundness (Interpretation), grouplike
--                    (Syntactics), the coset normal form
--                    (Normalization) and its uniqueness
--                    (UniqueNormalForm).  All of that is normalization
--                    work, and none of it says the semantics is onto.
--
--   presentation     promotes the sub-presentation with Surjectivity,
--                    which is the one thing normalization does not
--                    give.
--
-- The endofunction semantics stops at the first stage -- it is not
-- surjective -- which is what SubPresentation/ is about.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Presentation where

open import Presentation.Definitions
open import Normalization.StarPresentation

import Presentation.Properties as PP
import Relation.Binary.PropositionalEquality as Eq

open import Examples.Groups.Symmetric.Interpretation
open import Examples.Groups.Symmetric.Semantics
open import Examples.Groups.Symmetric.Syntactics

import Examples.Groups.Symmetric.Normalization as SN
import Examples.Groups.Symmetric.Surjectivity as Surj
import Examples.Groups.Symmetric.UniqueNormalForm as TU

------------------------------------------------------------------------
-- The sub-presentation

subpresentation : ∀ {n} → let open PP (n VRel,_===_) in
  (n VRel,_===_) IsSubPresentationOf (Permutation′-group n)
subpresentation {n} =
  GS.GetSubPresentation.groupSubPres sound-ax grouplike (SN.nfp'-t n)
                                     TU.unique-nf-tight-bundled
  where
  module GS = GroupSem (n VRel,_===_) (Eq.setoid (SN.NF n))
                       (Permutation′-group n) (⟦_⟧ᵍ {n})

------------------------------------------------------------------------
-- The presentation theorem

presentation : ∀ {n} → let open PP (n VRel,_===_) in
  (n VRel,_===_) IsPresentationOf (Permutation′-group n)
presentation {n} = isPresentationOf subpresentation (Surj.surjective {n})

------------------------------------------------------------------------
-- Presentations of groups
--
-- The endofunction semantics of Sₙ is a sub-presentation: ⟦_⟧ is a
-- setoid embedding of the word setoid into the endofunctions.
--
-- Both halves are collected here.  Soundness comes from
-- Interpretation; completeness -- words with equal denotations are
-- congruent -- is by normalization, from the unique normal form.
--
-- It stops here, and deliberately: promoting a sub-presentation to a
-- presentation needs the semantics to be onto, which endofunctions are
-- not.  _IsSubPresentationOf_ itself is not available to state, since
-- it is indexed by a Group and the endofunctions are only a monoid; the
-- pair below is the content it would carry.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.SubPresentation.SubPres where

open import Function.Definitions using (Congruent ; Injective)
open import Relation.Binary.Bundles using (Setoid)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP

open import Examples.Groups.Symmetric.SubPresentation.Semantics using (Endo-setoid ; ⟦_⟧)
open import Examples.Groups.Symmetric.SubPresentation.Interpretation using (sound)
open import Examples.Groups.Symmetric.Normalization using (NF)
open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)

import Examples.Groups.Symmetric.SubPresentation.UniqueNormalForm as LU


------------------------------------------------------------------------
-- Soundness: congruent words have equal denotations

soundness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Congruent (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧
soundness n = sound

------------------------------------------------------------------------
-- Completeness: words with equal denotations are congruent

completeness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Injective (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧
completeness n =
  NFBase.by-normalization (_VRel,_===_ n) (NF n) (Endo-setoid n) (⟦_⟧ {n})
    (LU.unique-nf n) sound

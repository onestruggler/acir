------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the normal form for a collapsing presentation.
--
-- The separation hypothesis -- distinct semantic values have distinct
-- normal forms -- is discharged by η for ⊤: there is only one normal
-- form to be had.
--
-- Parameterised by the same gen≈ε as Normalization; see the note there.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; [_]ʷ ; ε)

import Presentation.Base as PB

module Examples.Groups.Trivial.UniqueNormalForm
  {A : Set} (Γ : WRel A)
  (gen≈ε : ∀ x → PB._≈_ Γ [ x ]ʷ ε)
  where

open import Algebra.Bundles using (Group)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Normalization.NormalForm.Uniqueness using (UniqueNormalForm)

import Normalization.NormalForm.Setoid as SNF

open import Examples.Groups.Trivial.Semantics using (gp)

import Examples.Groups.Trivial.Interpretation as Intp
import Examples.Groups.Trivial.Normalization as Nrm

private
  module I = Intp Γ gen≈ε
  module N = Nrm Γ gen≈ε

------------------------------------------------------------------------
-- Any two normal forms coincide

unfp : UniqueNormalForm Γ (Eq.setoid ⊤) (Group.setoid gp) I.GS.⟦_⟧
         (SNF.NormalForm.inv-nf N.nfp')
unfp = record { unique = λ _ → Eq.refl }

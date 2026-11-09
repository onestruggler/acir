------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the permutation semantics of Sₙ: words with equal
-- denotations are congruent, by normalization.
--
-- The permutation counterpart of SubPresentation.SubPres's
-- completeness.  Symmetric-Prop's Presentation transports it, and
-- Examples.Groups.Alternating.Parity uses it: it makes the parity of a
-- circuit of transpositions an invariant of the permutation the
-- circuit denotes, which is how the sign of a permutation is defined
-- there.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Completeness where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Function.Definitions using (Injective)
open import Relation.Binary.Bundles using (Setoid)

import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Presentation.Properties as PP

open import Examples.Groups.Symmetric.Normalization using (NF ; nfp'-t)
open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
open import Examples.Groups.Symmetric.Interpretation using (⟦_⟧)
open import Examples.Groups.Symmetric.Soundness using (sound)

import Examples.Groups.Symmetric.UniqueNormalForm as TU

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Completeness of the tight semantics

completeness : let open PP (n VRel,_===_) in
  Injective (Setoid._≈_ word-setoid)
            (Setoid._≈_ (Group.setoid (Permutation′-group n))) ⟦_⟧
-- The normal form must be supplied explicitly: by-normalization takes
-- it implicitly, but its uniqueness argument mentions only the
-- section inv-nf, from which the record cannot be recovered.
completeness {n} =
  NFU.by-normalization (_VRel,_===_ n) (NF n)
    (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
    {nfp'-t n} TU.unique-nf-tight (sound {n})

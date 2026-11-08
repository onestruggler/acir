------------------------------------------------------------------------
-- Presentations of groups
--
-- The 3-qubit Toffoli-Hadamard group is presented by the circuits of
-- Circuits.Syntactics on three wires
--
-- A circuit denotes the scaled dyadic matrix of its reading in the
-- paper's alphabet (Circuits.Iso.ι); the reading is a group isomorphism
-- of the presented groups, and the paper's semantics, with the
-- definition of K, a group isomorphism onto L₈ (Repaired.Presentation),
-- so their composite is one too.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Circuits.Presentation where

import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Bundles using (Group)
open import Function using (_∘_)
open import Word.Base using (_ʷ)

open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+HH-3qubit.Circuits.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Circuits.Iso using (ι ; grouplike ; circuits≅paper)
import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation as P
open P using (ToffoliHadamard)

private
  module PP = _IsPresentationOf_ P.presentation

-- The matrix of a three-wire circuit.
⟦_⟧ : Circuit 3 → Group.Carrier ToffoliHadamard
⟦_⟧ = PP.⟦_⟧ ∘ (ι ʷ)

-- The relations present L₈, the exact orthogonal scaled dyadic 8 × 8
-- matrices.
presentation : (3 VRel,_===_) IsPresentationOf ToffoliHadamard
presentation = record
  { gl  = grouplike
  ; ⟦_⟧ = ⟦_⟧
  ; iso = Compose.isGroupIsomorphism {G₃ = Group.rawGroup ToffoliHadamard}
            (λ {i} {j} {k} → Group.trans ToffoliHadamard {i} {j} {k})
            {f = ι ʷ} {g = PP.⟦_⟧}
            circuits≅paper PP.iso
  }

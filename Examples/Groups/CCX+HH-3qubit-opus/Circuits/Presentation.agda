------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorems 5.2 and 6.3 for the circuits of Circuits.Syntactics: on three
-- wires, Σ₁ presents O(8, 𝔻) and Σ₂ presents TofH(3) = L₈
--
-- A circuit denotes the matrix of its reading in the paper's alphabet
-- (Circuits.Iso1.ι, Circuits.Iso2.ι); the reading is a group
-- isomorphism of the presented groups, and the paper's semantics a
-- group isomorphism onto O(8, 𝔻), resp. L₈ (PresentationO8,
-- PresentationH), so their composite is one too.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Circuits.Presentation where

import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Bundles using (Group)
open import Function using (_∘_)
open import Word.Base using (_ʷ)

open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+HH-3qubit-opus.Circuits.Syntactics using (module Σ₁ ; module Σ₂)
import Examples.Groups.CCX+HH-3qubit-opus.Circuits.Iso1 as I₁
import Examples.Groups.CCX+HH-3qubit-opus.Circuits.Iso2 as I₂
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics using (O8 ; TofH3)
import Examples.Groups.CCX+HH-3qubit-opus.PresentationO8 as O
import Examples.Groups.CCX+HH-3qubit-opus.PresentationH as H

private
  module PO = _IsPresentationOf_ O.presentation
  module PH = _IsPresentationOf_ H.presentation

------------------------------------------------------------------------
-- Theorem 5.2, with r_K: circuits over Σ₁ present O(8, 𝔻)

⟦_⟧₁ : Σ₁.Circuit 3 → Group.Carrier O8
⟦_⟧₁ = PO.⟦_⟧ ∘ (I₁.ι ʷ)

theorem-5-2 : (3 Σ₁.VRel,_===_) IsPresentationOf O8
theorem-5-2 = record
  { gl  = I₁.grouplike
  ; ⟦_⟧ = ⟦_⟧₁
  ; iso = Compose.isGroupIsomorphism {G₃ = Group.rawGroup O8}
            (λ {i} {j} {k} → Group.trans O8 {i} {j} {k})
            {f = I₁.ι ʷ} {g = PO.⟦_⟧}
            I₁.circuits≅paper PO.iso
  }

------------------------------------------------------------------------
-- Theorem 6.3, with r_K: circuits over Σ₂ present TofH(3)

⟦_⟧₂ : Σ₂.Circuit 3 → Group.Carrier TofH3
⟦_⟧₂ = PH.⟦_⟧ ∘ (I₂.ι ʷ)

theorem-6-3 : (3 Σ₂.VRel,_===_) IsPresentationOf TofH3
theorem-6-3 = record
  { gl  = I₂.grouplike
  ; ⟦_⟧ = ⟦_⟧₂
  ; iso = Compose.isGroupIsomorphism {G₃ = Group.rawGroup TofH3}
            (λ {i} {j} {k} → Group.trans TofH3 {i} {j} {k})
            {f = I₂.ι ʷ} {g = PH.⟦_⟧}
            I₂.circuits≅paper PH.iso
  }

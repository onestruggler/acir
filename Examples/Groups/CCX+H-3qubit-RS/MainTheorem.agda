------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Ross and Wesley (2024), through Li-Ross-Selinger: the main
-- theorem, for MainTheorems
--
-- R₂⁺ = Figures 4, 7 and 8, corrected, with r_K, presents L₈, the
-- group of 3-qubit Toffoli-Hadamard operators (scaled dyadic
-- orthogonal 8 × 8 matrices): Theorem 6.3, as circuits over
-- Circuit.Base on three wires (Circuits.Presentation) and over the
-- paper's alphabet (PresentationH), proved by translation into
-- Li-Ross-Selinger's presentation of L₈ (CCX+HH-TwoLevel.Scaled).  L₈
-- is a subgroup of U₈(𝔻[ω]) (DOmega), where a circuit's matrix is read
-- and compared.  This module collects what MainTheorems states, in the
-- format of CCX+H-3qubit-Tietze.MainTheorem, the other formalization of
-- the paper: the circuits, the relations (_CRel,_===_ at width three),
-- the group, a circuit's matrix ⟦_⟧, derivability ⊢_≈_, the
-- presentation, and its completeness and soundness for ⟦_⟧; and the
-- same for the paper's alphabet, marked ᴾ.  Theorem 5.2 (R₁⁺ presents
-- O₈(𝔻)) and the independence of r_K are in Theorems.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-RS.MainTheorem where

open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+H-3qubit-RS.Gates using (G₂)
open import Examples.Groups.CCX+H-3qubit-RS.Syntactics using (_===₂⁺_)
open import Examples.Groups.CCX+H-3qubit-RS.Circuits.Syntactics using (module Σ₂)
open Σ₂ public using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.CCX+H-3qubit-RS.Semantics public using () renaming (TofH3 to ToffoliHadamard)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.CCX+H-3qubit-RS.Circuits.Presentation as PC
import Examples.Groups.CCX+H-3qubit-RS.DOmega as Ω
import Examples.Groups.CCX+H-3qubit-RS.PresentationH as H

------------------------------------------------------------------------
-- Circuits on three wires

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

presentation : (3 CRel,_===_) IsPresentationOf ToffoliHadamard
presentation = PC.theorem-6-3

-- A circuit's matrix, over 𝔻[ω].
⟦_⟧ : Circuit 3 → UMat 8
⟦_⟧ = Ω.circuit⟦_⟧₂

complete : ∀ {w v : Circuit 3} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.circuit-complete₂

sound : ∀ {w v : Circuit 3} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.circuit-sound₂

------------------------------------------------------------------------
-- The paper's alphabet

Wordᴾ : Set
Wordᴾ = Word G₂

-- R₂⁺: the relations of Figures 4, 7 and 8, corrected, with r_K.
infix 4 _===ᴾ_
_===ᴾ_ : WRel G₂
_===ᴾ_ = _===₂⁺_

-- Equality by them.
infix 4 ⊢ᴾ_≈_
⊢ᴾ_≈_ : Wordᴾ → Wordᴾ → Set
⊢ᴾ_≈_ = PB._≈_ _===ᴾ_

presentationᴾ : _===ᴾ_ IsPresentationOf ToffoliHadamard
presentationᴾ = H.presentation

-- A word's matrix, over 𝔻[ω].
⟦_⟧ᴾ : Wordᴾ → UMat 8
⟦_⟧ᴾ = Ω.⟦_⟧₂

completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
completeᴾ = Ω.complete₂

soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
soundᴾ = Ω.sound₂

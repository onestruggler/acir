------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger (2023): the main theorem, for MainTheorems
--
-- The relations of Figure 1 present the two-qubit Clifford+T group in
-- U₄(ℤ[1/√2, i]) = U₄(𝔻[ω]), as circuits over Circuit.Base on two wires
-- (Circuits.Presentation) and over the paper's alphabet
-- (Presentation).  This module collects what MainTheorems states,
-- behind one import: the circuits, the relations (_CRel,_===_ at width
-- two), the group, a circuit's matrix ⟦_⟧, derivability ⊢_≈_, the
-- sub-presentation, and its completeness and soundness for ⟦_⟧; and the
-- same for the paper's alphabet, marked ᴾ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.MainTheorem where

open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
open Clifford+T using (Generator ; Rel)
open import Examples.Groups.Clifford+T-2qubit.Circuits.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Clifford+T-2qubit.Circuits.Presentation as PC
import Examples.Groups.Clifford+T-2qubit.Presentation as P

------------------------------------------------------------------------
-- Circuits on two wires

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

presentation : (2 CRel,_===_) IsSubPresentationOf U 4
presentation = PC.presentation

-- A circuit's matrix.
⟦_⟧ : Circuit 2 → UMat 4
⟦_⟧ = PC.⟦_⟧

complete : ∀ {w v : Circuit 2} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = PE.Sub.complete presentation

sound : ∀ {w v : Circuit 2} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = PE.Sub.sound presentation

------------------------------------------------------------------------
-- The paper's alphabet

Wordᴾ : Set
Wordᴾ = Word Generator

-- The relations of Figure 1.
infix 4 _===ᴾ_
_===ᴾ_ : WRel Generator
_===ᴾ_ = Rel

-- Equality by them.
infix 4 ⊢ᴾ_≈_
⊢ᴾ_≈_ : Wordᴾ → Wordᴾ → Set
⊢ᴾ_≈_ = PB._≈_ _===ᴾ_

presentationᴾ : _===ᴾ_ IsSubPresentationOf U 4
presentationᴾ = P.presentation

-- A word's matrix.
⟦_⟧ᴾ : Wordᴾ → UMat 4
⟦_⟧ᴾ = P.⟦_⟧

completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
completeᴾ = P.complete

soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
soundᴾ = P.sound

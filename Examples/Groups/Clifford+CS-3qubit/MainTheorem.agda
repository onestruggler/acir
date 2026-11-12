------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger (2023): the main theorem, for MainTheorems
--
-- The relations of Figure 2 present the three-qubit Clifford+CS group
-- in U₈(ℤ[½, i]), as circuits over Circuit.Base on three wires
-- (Circuits.Presentation) and over the paper's alphabet
-- (Presentation).  U₈(ℤ[½, i]) is a subgroup of U₈(𝔻[ω]) (DOmega),
-- where a circuit's matrix is read and compared.  This module collects
-- what MainTheorems states, behind one import: the circuits, the
-- relations (_CRel,_===_ at width three), the group, a circuit's
-- matrix ⟦_⟧, derivability ⊢_≈_, the sub-presentation, and its
-- completeness and soundness for ⟦_⟧; and the same for the paper's
-- alphabet, marked ᴾ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-3qubit.MainTheorem where

open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
open CliffordCS using (Gen ; Rel)
open import Examples.Groups.Clifford+CS-3qubit.Circuits.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Clifford+CS-3qubit.Circuits.Presentation as PC
import Examples.Groups.Clifford+CS-3qubit.DOmega as Ω
import Examples.Groups.Clifford+CS-3qubit.Presentation as P

------------------------------------------------------------------------
-- Circuits on three wires

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

presentation : (3 CRel,_===_) IsSubPresentationOf U 8
presentation = PC.presentation

-- A circuit's matrix, over 𝔻[ω].
⟦_⟧ : Circuit 3 → UMat 8
⟦_⟧ = Ω.circuit⟦_⟧

complete : ∀ {w v : Circuit 3} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.circuit-complete

sound : ∀ {w v : Circuit 3} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.circuit-sound

------------------------------------------------------------------------
-- The paper's alphabet

Wordᴾ : Set
Wordᴾ = Word Gen

-- The relations of Figure 2.
infix 4 _===ᴾ_
_===ᴾ_ : WRel Gen
_===ᴾ_ = Rel

-- Equality by them.
infix 4 ⊢ᴾ_≈_
⊢ᴾ_≈_ : Wordᴾ → Wordᴾ → Set
⊢ᴾ_≈_ = PB._≈_ _===ᴾ_

presentationᴾ : _===ᴾ_ IsSubPresentationOf U 8
presentationᴾ = P.presentation

-- A word's matrix, over 𝔻[ω].
⟦_⟧ᴾ : Wordᴾ → UMat 8
⟦_⟧ᴾ = Ω.⟦_⟧

completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
completeᴾ = Ω.complete

soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
soundᴾ = Ω.sound

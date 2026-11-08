------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Ross and Wesley (2024): the main theorem, for MainTheorems
--
-- The relations of Figures 4, 7 and 8, corrected and with the
-- definition of K that Section 5.5 uses but the figures omit, present
-- L₈, the group of 3-qubit Toffoli-Hadamard operators (scaled dyadic
-- orthogonal 8 × 8 matrices), as circuits over Circuit.Base on three
-- wires (Circuits.Presentation) and over the paper's alphabet
-- (Repaired.Presentation).  L₈ is a subgroup of U₈(𝔻[ω]) (DOmega),
-- where a circuit's matrix is read and compared.  This module collects
-- what MainTheorems states, behind one import: the circuits, the
-- relations (_CRel,_===_ at width three), the group, a circuit's
-- matrix ⟦_⟧, derivability ⊢_≈_, the presentation, and its
-- completeness and soundness for ⟦_⟧; and the same for the paper's
-- alphabet, marked ᴾ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.MainTheorem where

open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+H-3qubit-Tietze.Repaired.Syntactics using (Gen ; _===_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Circuits.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Repaired.Presentation public using (ToffoliHadamard)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.CCX+H-3qubit-Tietze.Circuits.Presentation as PC
import Examples.Groups.CCX+H-3qubit-Tietze.DOmega as Ω
import Examples.Groups.CCX+H-3qubit-Tietze.Repaired.Presentation as P

------------------------------------------------------------------------
-- Circuits on three wires

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

presentation : (3 CRel,_===_) IsPresentationOf ToffoliHadamard
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

-- The relations of Figures 4, 7 and 8, repaired.
infix 4 _===ᴾ_
_===ᴾ_ : WRel Gen
_===ᴾ_ = _===_

-- Equality by them.
infix 4 ⊢ᴾ_≈_
⊢ᴾ_≈_ : Wordᴾ → Wordᴾ → Set
⊢ᴾ_≈_ = PB._≈_ _===ᴾ_

presentationᴾ : _===ᴾ_ IsPresentationOf ToffoliHadamard
presentationᴾ = P.presentation

-- A word's matrix, over 𝔻[ω].
⟦_⟧ᴾ : Wordᴾ → UMat 8
⟦_⟧ᴾ = Ω.⟦_⟧

completeᴾ : ∀ {w v : Wordᴾ} → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ → ⊢ᴾ w ≈ v
completeᴾ = Ω.complete

soundᴾ : ∀ {w v : Wordᴾ} → ⊢ᴾ w ≈ v → ⟦ w ⟧ᴾ ≈ᵁ ⟦ v ⟧ᴾ
soundᴾ = Ω.sound

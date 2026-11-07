------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger (2015): the main theorem, for MainTheorems
--
-- The gates ω, H, S, CZ and the relations C1–C15 of Figure 8 present
-- the group the circuits on n wires generate in U_{2ⁿ}(𝔻[ω]), at every
-- width (Presentation.DOmega, Proposition 7.1 at 𝔻[ω]).  This module
-- collects what MainTheorems states, behind one import: the circuits,
-- the relations at each width (_CRel,_===_), the group, a circuit's
-- matrix ⟦_⟧, derivability ⊢_≈_, the sub-presentation, and its
-- completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.MainTheorem where

open import Data.Nat.Base using (ℕ ; _^_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Qubit-Clifford.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Qubit-Clifford.Presentation.DOmega as P

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation n = P.presentation {n}

-- A circuit's matrix.
⟦_⟧ : ∀ {n} → Circuit n → UMat (2 ^ n)
⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete {n} = PE.Sub.complete (presentation n)

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound {n} = PE.Sub.sound (presentation n)

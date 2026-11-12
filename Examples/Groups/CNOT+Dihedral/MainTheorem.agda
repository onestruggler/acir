------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Chen and Ross (2018): the main theorem, for MainTheorems
--
-- The gates ω, X, T, CNOT and the relations R₁–R₁₃ of Figure 1, with
-- the swap rules, present the group the circuits on n wires generate in
-- U_{2ⁿ}(𝔻[ω]), at every width.  This module collects what MainTheorems
-- states, behind one import: the circuits, the relations at each width
-- (_CRel,_===_), the group, a circuit's matrix ⟦_⟧, derivability ⊢_≈_,
-- the sub-presentation, and its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CNOT+Dihedral.MainTheorem where

open import Data.Nat.Base using (ℕ ; _^_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.CNOT+Dihedral.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.CNOT+Dihedral.Presentation as P

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

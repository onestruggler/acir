------------------------------------------------------------------------
-- Presentations of groups
--
-- Makary, Ross and Selinger (2021): the main theorem, for MainTheorems
--
-- The gates −1, H, Z, CZ and the relations R1–R16 of Figure 1 present
-- the group the circuits on n wires generate, at every width, in
-- U_{2ⁿ}(𝔻[ω]) (Presentation.DOmega) and in O_{2ⁿ}(ℤ[1/√2])
-- (Presentation.DRootTwo).  This module collects what MainTheorems
-- states, behind one import: the circuits, the relations at each width
-- (_CRel,_===_), the two groups, a circuit's matrix ⟦_⟧ over 𝔻[ω],
-- derivability ⊢_≈_, the two sub-presentations, and completeness and
-- soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.MainTheorem where

open import Data.Nat.Base using (ℕ ; _^_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Real-Clifford.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (U)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics public using (O)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Real-Clifford.Presentation.DOmega as PU
import Examples.Groups.Real-Clifford.Presentation.DRootTwo as PO

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation n = PU.presentation {n}

presentationᴼ : ∀ n → (n CRel,_===_) IsSubPresentationOf O (2 ^ n)
presentationᴼ n = PO.presentation {n}

-- A circuit's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Circuit n → UMat (2 ^ n)
⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete {n} = PE.Sub.complete (presentation n)

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound {n} = PE.Sub.sound (presentation n)

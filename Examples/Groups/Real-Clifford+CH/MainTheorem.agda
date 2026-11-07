------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément (2026): the main theorem, for MainTheorems
--
-- The gates H, Z, CZ, CH and the relations of Figure 4 present the group
-- the circuits on n wires generate in O_{2ⁿ}(ℤ[1/√2]), at every width:
-- Theorem 8.9, with Theorem 4.4, which the paper imports from
-- Hadamard-Π, proved from Clément's thesis (Presentation).
-- O_{2ⁿ}(ℤ[1/√2]) is a subgroup of U_{2ⁿ}(𝔻[ω]) (DOmega), where a
-- circuit's matrix is read and compared.  This module collects what
-- MainTheorems states, behind one import: the circuits, the relations
-- at each width (_CRel,_===_), the group, a circuit's matrix ⟦_⟧,
-- derivability ⊢_≈_, the sub-presentation, and its completeness and
-- soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.MainTheorem where

open import Data.Nat.Base using (ℕ ; _^_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Real-Clifford+CH.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics public using (O)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Real-Clifford+CH.DOmega as Ω
import Examples.Groups.Real-Clifford+CH.Presentation as P

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf O (2 ^ n)
presentation = P.subpresentationᴼ

-- A circuit's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Circuit n → UMat (2 ^ n)
⟦_⟧ = Ω.⟦_⟧

complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.complete

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.sound

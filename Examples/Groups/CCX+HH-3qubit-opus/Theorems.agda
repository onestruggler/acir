------------------------------------------------------------------------
-- Presentations of groups
--
-- The main results on Amy, Ross and Wesley, "A Sound and Complete
-- Equational Theory for 3-Qubit Toffoli-Hadamard Circuits" (QPL 2024,
-- arXiv:2407.11152), restated.
--
-- The presentations are with r_K, the relation K₁₂ = X₀ NK X₀ NK of
-- the paper's Section 5.5, which Figures 4 and 7 omit and which does
-- not follow from them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Theorems where

open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Word.Base using (Word ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics

import Examples.Groups.CCX+HH-3qubit-opus.SoundnessH as Sound
import Examples.Groups.CCX+HH-3qubit-opus.PresentationO8 as O8
import Examples.Groups.CCX+HH-3qubit-opus.PresentationH as H
import Examples.Groups.CCX+HH-3qubit-opus.Independence as I

------------------------------------------------------------------------
-- O(8, 𝔻): circuits over Σ₁ = 𝒟 ∪ {K_[0,1,2,3], CCZ}

-- Soundness and completeness of R₁⁺ = R₀ ∪ R₈₄ ∪ {r_K}.
soundness₁ : {w v : Word G₁} → PB._≈_ _===₁⁺_ w v → ⟦ w ⟧ ≡ ⟦ v ⟧
soundness₁ = Sound.sound₁⁺*

completeness₁ : {w v : Word G₁} → ⟦ w ⟧ ≡ ⟦ v ⟧ → PB._≈_ _===₁⁺_ w v
completeness₁ = O8.complete₁

-- Theorem 5.2, with r_K.
theorem-5-2 : _===₁⁺_ IsPresentationOf O8
theorem-5-2 = O8.presentation

------------------------------------------------------------------------
-- TofH(3): circuits over Σ₂ = Σ₁ ∪ {H₂}

-- Soundness and completeness of R₂⁺ = R₁⁺ ∪ Figure 8.
soundness₂ : {w v : Word G₂} → PB._≈_ _===₂⁺_ w v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
soundness₂ = Sound.sound₂⁺*

completeness₂ : {w v : Word G₂} → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ → PB._≈_ _===₂⁺_ w v
completeness₂ = H.complete₂

-- Theorem 6.3, with r_K.
theorem-6-3 : _===₂⁺_ IsPresentationOf TofH3
theorem-6-3 = H.presentation

------------------------------------------------------------------------
-- r_K is needed

-- It holds of the matrices but is not derivable from R₁ = R₀ ∪ R₈₄.
r_K-independent : ⟦ K12 {1} ⟧ ≡ ⟦ X0 • NKw {0} • X0 • NKw ⟧ ×
                  ¬ PB._≈_ _===₁_ K12 (X0 • NKw • X0 • NKw)
r_K-independent = I.R₁-incomplete

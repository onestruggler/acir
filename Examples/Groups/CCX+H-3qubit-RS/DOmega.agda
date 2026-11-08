------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Ross and Wesley's 3-qubit Toffoli-Hadamard circuits, read in
-- U₈(𝔻[ω]), by the route through Li-Ross-Selinger's presentations
--
-- R₁⁺ presents O₈(𝔻) (Theorem 5.2) and R₂⁺ presents L₈ (Theorem 6.3),
-- over the paper's alphabet (PresentationO8, PresentationH) and as
-- circuits on three wires (Circuits.Presentation).  Both groups are
-- subgroups of U₈(𝔻[ω]): O₈(𝔻) by CCX+HH-TwoLevel.DOmega, L₈ by EmbedL,
-- at the dimension 8 itself, as in CCX+H-3qubit-Tietze.DOmega.  So all
-- four presentations are sub-presentations of U₈(𝔻[ω]): two words, or
-- two circuits, are equal by the relations exactly when their matrices
-- over 𝔻[ω] are equal (sound₁, complete₁, …; circuit-sound₁, …).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-RS.DOmega where

open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.CCX+H-3qubit-RS.Syntactics using (_===₁⁺_ ; _===₂⁺_)
open import Examples.Groups.CCX+H-3qubit-RS.Circuits.Syntactics using (module Σ₁ ; module Σ₂)
open import Examples.Groups.CCX+H-3qubit-RS.Semantics using (TofH3)
import Examples.Groups.CCX+H-3qubit-RS.PresentationO8 as O
import Examples.Groups.CCX+H-3qubit-RS.PresentationH as H
import Examples.Groups.CCX+H-3qubit-RS.Circuits.Presentation as PC
import Examples.Groups.CCX+HH-TwoLevel.DOmega as CΩ
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

-- L₈ in U₈(𝔻[ω]).
module EmbedL =
  RΩ.Emb.Group-Embedding TofH3 8 proj₁ (λ x → proj₁ (proj₂ x))
    (λ e → e) (λ e → e) (λ _ _ → refl) refl

------------------------------------------------------------------------
-- Theorem 5.2: R₁⁺ and O₈(𝔻)

presentation₁ : _===₁⁺_ IsSubPresentationOf U 8
presentation₁ = CΩ.Embed.along-presentation 8 O.presentation

open PE.Sub presentation₁ public
  renaming (⟦_⟧ to ⟦_⟧₁ ; sound to sound₁ ; complete to complete₁)

circuit-presentation₁ : (3 Σ₁.VRel,_===_) IsSubPresentationOf U 8
circuit-presentation₁ = CΩ.Embed.along-presentation 8 PC.theorem-5-2

open PE.Sub circuit-presentation₁ public
  renaming (⟦_⟧ to circuit⟦_⟧₁ ; sound to circuit-sound₁ ; complete to circuit-complete₁)

------------------------------------------------------------------------
-- Theorem 6.3: R₂⁺ and L₈

presentation₂ : _===₂⁺_ IsSubPresentationOf U 8
presentation₂ = EmbedL.along-presentation H.presentation

open PE.Sub presentation₂ public
  renaming (⟦_⟧ to ⟦_⟧₂ ; sound to sound₂ ; complete to complete₂)

circuit-presentation₂ : (3 Σ₂.VRel,_===_) IsSubPresentationOf U 8
circuit-presentation₂ = EmbedL.along-presentation PC.theorem-6-3

open PE.Sub circuit-presentation₂ public
  renaming (⟦_⟧ to circuit⟦_⟧₂ ; sound to circuit-sound₂ ; complete to circuit-complete₂)

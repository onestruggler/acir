------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Ross and Wesley's 3-qubit Toffoli-Hadamard circuits, read in
-- U₈(𝔻[ω])
--
-- The repaired relations present L₈, the orthogonal scaled dyadic 8 × 8
-- matrices (Repaired.Presentation, over the paper's alphabet;
-- Circuits.Presentation, as circuits on three wires), and L₈ is a
-- subgroup of U₈(𝔻[ω]) (Embed, as CCX+HH-TwoLevel.Scaled.DOmega's EmbedL),
-- so both are sub-presentations of U₈(𝔻[ω]): two words, or two
-- circuits, are equal by the relations exactly when their matrices
-- over 𝔻[ω] are equal (sound, complete; circuit-sound,
-- circuit-complete).
--
-- Embed is stated at the dimension 8 itself rather than taken from
-- EmbedL 3, whose dimension is spelled suc 3 * 2: compared with U 8,
-- the group U (suc 3 * 2) is unfolded and compared field by field,
-- proofs included, which did not finish in 45 minutes.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.DOmega where

open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics using (_===_)
import Examples.Groups.CCX+HH-3qubit.Circuits.Syntactics as C
import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation as P
import Examples.Groups.CCX+HH-3qubit.Circuits.Presentation as PC
open import Examples.Groups.CCX+HH-3qubit.Repaired.Presentation using (ToffoliHadamard)
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

-- L₈ in U₈(𝔻[ω]).
module Embed =
  RΩ.Emb.Group-Embedding ToffoliHadamard 8 proj₁ (λ x → proj₁ (proj₂ x))
    (λ e → e) (λ e → e) (λ _ _ → refl) refl

-- Over the paper's alphabet ...
presentation : _===_ IsSubPresentationOf U 8
presentation = Embed.along-presentation P.presentation

open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

-- ... and as circuits.
circuit-presentation : C._VRel,_===_ 3 IsSubPresentationOf U 8
circuit-presentation = Embed.along-presentation PC.presentation

open PE.Sub circuit-presentation public
  renaming (⟦_⟧ to circuit⟦_⟧ ; sound to circuit-sound ; complete to circuit-complete)

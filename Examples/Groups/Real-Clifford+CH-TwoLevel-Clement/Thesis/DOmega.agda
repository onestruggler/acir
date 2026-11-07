------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's own proof, read in Uₙ(𝔻[ω])
--
-- Oₙ(𝔻[√2]) is a subgroup of Uₙ(𝔻[ω]) (Real-Clifford+CH-TwoLevel.
-- DOmega), so the two presentations of Thesis.Presentation — Clément's
-- relations (1)–(21) and Figure 6, by his Algorithm 1 and Theorem 4.1
-- — are sub-presentations of Uₙ(𝔻[ω]): two words are equal by
-- Clément's relations (soundᶜ, completeᶜ), or by Figure 6 (sound,
-- complete), exactly when their matrices over 𝔻[ω] are equal.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.DOmega where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (_===_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Presentation as T
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

module _ {n : ℕ} where

  -- Clément's relations ...
  presentationᶜ : (_===ᶜ_ {n}) IsSubPresentationOf U n
  presentationᶜ = RΩ.Embed.along-presentation n (T.presentationᶜ {n})

  open PE.Sub presentationᶜ public using (⟦_⟧) renaming (sound to soundᶜ ; complete to completeᶜ)

  -- ... and Figure 6, with the same semantics.
  presentation : (_===_ {n}) IsSubPresentationOf U n
  presentation = RΩ.Embed.along-presentation n (T.presentation {n})

  sound : ∀ {w v} → PB._≈_ (_===_ {n}) w v → Group._≈_ (U n) ⟦ w ⟧ ⟦ v ⟧
  sound = PE.Sub.sound presentation

  complete : ∀ {w v} → Group._≈_ (U n) ⟦ w ⟧ ⟦ v ⟧ → PB._≈_ (_===_ {n}) w v
  complete = PE.Sub.complete presentation

------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 6 and Clément's relations, read in Uₙ(𝔻[ω])
--
-- Oₙ(𝔻[√2]) is a subgroup of Uₙ(𝔻[ω]) (Real-Clifford+CH-TwoLevel.
-- DOmega), so the two presentations of Presentation — Hadamard-Pi's
-- Figure 6, unconditional now that the hard case is proved, and
-- Clément's relations (1)–(21) — are sub-presentations of Uₙ(𝔻[ω]).
-- Both read a word as its matrix over 𝔻[ω] (⟦_⟧, its matrix over
-- 𝔻[√2] with the entries included), and two words are equal by either
-- set of relations exactly when those matrices are equal (sound,
-- complete; soundᶜ, completeᶜ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.DOmega where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Matrix using (matrix-map)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics as S
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation as C
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

module _ {n : ℕ} where

  -- Figure 6 ...
  presentation : (_===_ {n}) IsSubPresentationOf U n
  presentation = RΩ.Embed.along-presentation n (C.presentation {n})

  open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

  -- ... and Clément's relations, with the same semantics.
  presentationᶜ : (_===ᶜ_ {n}) IsSubPresentationOf U n
  presentationᶜ = RΩ.Embed.along-presentation n (C.presentationᶜ {n})

  soundᶜ : ∀ {w v} → PB._≈_ (_===ᶜ_ {n}) w v → Group._≈_ (U n) ⟦ w ⟧ ⟦ v ⟧
  soundᶜ = PE.Sub.sound presentationᶜ

  completeᶜ : ∀ {w v} → Group._≈_ (U n) ⟦ w ⟧ ⟦ v ⟧ → PB._≈_ (_===ᶜ_ {n}) w v
  completeᶜ = PE.Sub.complete presentationᶜ

  -- A word's matrix over 𝔻[ω] is its matrix over 𝔻[√2], included.
  ⟦⟧-matrix : (w : Word (Gen n)) → proj₁ ⟦ w ⟧ ≡ matrix-map RΩ.ι S.⟦ w ⟧ᵐ
  ⟦⟧-matrix w = refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- Li, Ross and Selinger's presentation of Lₙ, read in Uₙ(𝔻[ω])
--
-- Lₙ, the orthogonal scaled dyadic matrices N / √2ʲ (n = 2(k + 1)),
-- has its entries in 𝔻[√2] = ℤ[1/√2], a subring of 𝔻[ω] = ℤ[1/√2, i]
-- (Real-Clifford+CH-TwoLevel.DOmega.Emb), so it is a subgroup of
-- Uₙ(𝔻[ω]) (EmbedL), and Tables 1 and 2, which present Lₙ
-- (Presentation), are a sub-presentation of Uₙ(𝔻[ω]): two words are
-- equal by the tables exactly when their matrices over 𝔻[ω] are equal
-- (sound, complete).  The dimension is spelled suc k * 2 throughout;
-- CCX+H-3qubit-Tietze.DOmega embeds L₈ at the dimension 8 itself,
-- since U 8 and U (suc 3 * 2) are compared by unfolding both groups.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scaled.DOmega where

open import Data.Nat.Base as ℕ using (ℕ ; suc)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (_===ᴸ_)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation as PL
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

------------------------------------------------------------------------
-- Lₙ in Uₙ(𝔻[ω]), n = 2(k + 1)

module EmbedL (k : ℕ) =
  RΩ.Emb.Group-Embedding (PL.L k) (suc k ℕ.* 2) proj₁ (λ x → proj₁ (proj₂ x))
    (λ e → e) (λ e → e) (λ _ _ → refl) refl

------------------------------------------------------------------------
-- The presentation, read in Uₙ(𝔻[ω])

module _ (k : ℕ) where

  presentation : (_===ᴸ_ {suc k ℕ.* 2}) IsSubPresentationOf U (suc k ℕ.* 2)
  presentation = EmbedL.along-presentation k (PL.presentation k)

  open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

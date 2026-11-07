------------------------------------------------------------------------
-- Presentations of groups
--
-- Li, Ross and Selinger's presentation of Oₙ(𝔻), read in Uₙ(𝔻[ω])
--
-- 𝔻 = ℤ[½] is a subring of 𝔻[ω] = ℤ[1/√2, i] (EucDomain's base→ω), an
-- injective ring homomorphism that commutes with conjugation (the
-- identity on 𝔻).  So Oₙ(𝔻) is a subgroup of Uₙ(𝔻[ω]) (Embed), and
-- Table 1, which presents Oₙ(𝔻) (Presentation), is a sub-presentation
-- of Uₙ(𝔻[ω]): a word's matrix over 𝔻[ω] is its matrix over 𝔻 with the
-- entries included (⟦⟧-matrix), and two words are equal by Table 1
-- exactly when those matrices are equal (sound, complete).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.DOmega where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Matrix using (matrix-map)
import Quantum.Synthesis.Ring as QR
import Quantum.Synthesis.Ring.Properties.Embedding as E

open import Word.Base using (Word)
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; _===_)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Presentation as P
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring as Ω
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U ; UMat)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Subring as Subring

------------------------------------------------------------------------
-- 𝔻 in 𝔻[ω], with the (opaque) operations of both

ι : R.D → Ω.D
ι = E.base→ω ⦃ QR.RingDyadic ⦄

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.adjᴰ Ω._+ᴰ_ Ω._*ᴰ_ Ω.adjᴰ

  ι-+ : ∀ x y → ι (x R.DR.+ y) ≡ ι x Ω.DR.+ ι y
  ι-+ = E.At-𝔻.base→ω-+

  ι-* : ∀ x y → ι (x R.DR.* y) ≡ ι x Ω.DR.* ι y
  ι-* = E.At-𝔻.base→ω-*

  ι-adj : ∀ x → ι (R.adjᴰ x) ≡ Ω.adjᴰ (ι x)
  ι-adj = E.At-𝔻.base→ω-adj

-- Matrices over 𝔻 as matrices over 𝔻[ω].
module Emb = Subring {A = R.D} ⦃ R.RingD ⦄ ⦃ R.AdjointD ⦄ R.isCommutativeRing-D R.adj-D
               ι ι-+ ι-* refl refl ι-adj (E.base→ω-injective ⦃ QR.RingDyadic ⦄)

------------------------------------------------------------------------
-- Oₙ(𝔻) in Uₙ(𝔻[ω])

module Embed (n : ℕ) =
  Emb.Group-Embedding (S.O n) n proj₁ proj₂ (λ e → e) (λ e → e) (λ _ _ → refl) refl

------------------------------------------------------------------------
-- The presentation, read in Uₙ(𝔻[ω])

module _ {n : ℕ} where

  presentation : (_===_ {n}) IsSubPresentationOf U n
  presentation = Embed.along-presentation n (P.presentation {n})

  open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

  -- A word's matrix over 𝔻[ω] is its matrix over 𝔻, included.
  ⟦⟧-matrix : (w : Word (Gen n)) → proj₁ ⟦ w ⟧ ≡ matrix-map ι S.⟦ w ⟧ᵐ
  ⟦⟧-matrix w = refl

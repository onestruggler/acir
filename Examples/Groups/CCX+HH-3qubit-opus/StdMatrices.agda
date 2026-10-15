------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuits T d of Figure 7 and (-1)_[0] encode words with the
-- matrices of X_[d,d+1] and (-1)_[0], checked by computing them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.StdMatrices where

open import Data.Fin using (#_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  mT0 : S1.⟦ encʷ (T {1} 0) ⟧ᵐ ≡ S1.⟦ X[ # 0 , # 1 ] ⟧ᵐ
  mT0 = refl

  mT1 : S1.⟦ encʷ (T {1} 1) ⟧ᵐ ≡ S1.⟦ X[ # 1 , # 2 ] ⟧ᵐ
  mT1 = refl

  mT2 : S1.⟦ encʷ (T {1} 2) ⟧ᵐ ≡ S1.⟦ X[ # 2 , # 3 ] ⟧ᵐ
  mT2 = refl

  mT3 : S1.⟦ encʷ (T {1} 3) ⟧ᵐ ≡ S1.⟦ X[ # 3 , # 4 ] ⟧ᵐ
  mT3 = refl

  mT4 : S1.⟦ encʷ (T {1} 4) ⟧ᵐ ≡ S1.⟦ X[ # 4 , # 5 ] ⟧ᵐ
  mT4 = refl

  mT5 : S1.⟦ encʷ (T {1} 5) ⟧ᵐ ≡ S1.⟦ X[ # 5 , # 6 ] ⟧ᵐ
  mT5 = refl

  mT6 : S1.⟦ encʷ (T {1} 6) ⟧ᵐ ≡ S1.⟦ X[ # 6 , # 7 ] ⟧ᵐ
  mT6 = refl

  mm0 : S1.⟦ encʷ (m0 {0}) ⟧ᵐ ≡ S1.⟦ M[ # 0 ] ⟧ᵐ
  mm0 = refl

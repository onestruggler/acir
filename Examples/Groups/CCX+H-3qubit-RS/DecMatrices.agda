------------------------------------------------------------------------
-- Presentations of groups
--
-- The decodings of the basic generators (-1)_[0], X_[d,d+1] and
-- K_[0,1,2,3] of Li, Ross and Selinger have their matrices, checked by
-- computing them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.DecMatrices where

open import Data.Fin using (#_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using ([_]ʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1

open import Examples.Groups.CCX+HH-3qubit-opus.Encoding
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter₁ using (dec)

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  dM0 : ⟦ dec (M-gen (# 0)) ⟧ ≡ S1.⟦ M[ # 0 ] ⟧ᵐ
  dM0 = refl

  dX01 : ⟦ dec (X-gen (# 0) (# 1) (lt (# 0) (# 1))) ⟧ ≡ S1.⟦ X[ # 0 , # 1 ] ⟧ᵐ
  dX01 = refl

  dX12 : ⟦ dec (X-gen (# 1) (# 2) (lt (# 1) (# 2))) ⟧ ≡ S1.⟦ X[ # 1 , # 2 ] ⟧ᵐ
  dX12 = refl

  dX23 : ⟦ dec (X-gen (# 2) (# 3) (lt (# 2) (# 3))) ⟧ ≡ S1.⟦ X[ # 2 , # 3 ] ⟧ᵐ
  dX23 = refl

  dX34 : ⟦ dec (X-gen (# 3) (# 4) (lt (# 3) (# 4))) ⟧ ≡ S1.⟦ X[ # 3 , # 4 ] ⟧ᵐ
  dX34 = refl

  dX45 : ⟦ dec (X-gen (# 4) (# 5) (lt (# 4) (# 5))) ⟧ ≡ S1.⟦ X[ # 4 , # 5 ] ⟧ᵐ
  dX45 = refl

  dX56 : ⟦ dec (X-gen (# 5) (# 6) (lt (# 5) (# 6))) ⟧ ≡ S1.⟦ X[ # 5 , # 6 ] ⟧ᵐ
  dX56 = refl

  dX67 : ⟦ dec (X-gen (# 6) (# 7) (lt (# 6) (# 7))) ⟧ ≡ S1.⟦ X[ # 6 , # 7 ] ⟧ᵐ
  dX67 = refl

  dK0123 : ⟦ dec (K-gen (# 0) (# 1) (# 2) (# 3) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))) ⟧ ≡
           S1.⟦ K[ # 0 , # 1 , # 2 , # 3 ] ⟧ᵐ
  dK0123 = refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrices behind Table 2 of Li, Ross and Selinger (I ⊗ H = H₂):
-- for each relation H g H = t, H₂'s conjugate (Push.conj) of the
-- decoding of g has the matrix of the decoding of t.  Checked by
-- computing them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.TableMatrices where

open import Data.Fin using (#_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using (Word ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding using (lt)
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter₁ using (dec)
open import Examples.Groups.CCX+HH-3qubit-opus.Push using (conj)
open import Examples.Groups.CCX+HH-3qubit-opus.PushMatrices using (⟦_⟧₁)

-- The letters of Table 2, decoded.
M0 M1 M3 M5 M7 X01 X12 X23 X34 X45 X56 X67 K0123 K2345 K4567 : Word G₁
M0 = dec (M-gen (# 0))
M1 = dec (M-gen (# 1))
M3 = dec (M-gen (# 3))
M5 = dec (M-gen (# 5))
M7 = dec (M-gen (# 7))
X01 = dec (X-gen (# 0) (# 1) (lt (# 0) (# 1)))
X12 = dec (X-gen (# 1) (# 2) (lt (# 1) (# 2)))
X23 = dec (X-gen (# 2) (# 3) (lt (# 2) (# 3)))
X34 = dec (X-gen (# 3) (# 4) (lt (# 3) (# 4)))
X45 = dec (X-gen (# 4) (# 5) (lt (# 4) (# 5)))
X56 = dec (X-gen (# 5) (# 6) (lt (# 5) (# 6)))
X67 = dec (X-gen (# 6) (# 7) (lt (# 6) (# 7)))
K0123 = dec (K-gen (# 0) (# 1) (# 2) (# 3) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3)))
K2345 = dec (K-gen (# 2) (# 3) (# 4) (# 5) (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5)))
K4567 = dec (K-gen (# 4) (# 5) (# 6) (# 7) (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7)))

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  -- (7b)
  t7b : ⟦ (conj ʷ) K0123 ⟧₁ ≡ ⟦ K0123 ⟧₁
  t7b = refl

  -- (7c)
  t7c : ⟦ (conj ʷ) M0 ⟧₁ ≡ ⟦ M0 • X01 • M0 ⟧₁
  t7c = refl

  -- (7d), x even.
  t7d0 : ⟦ (conj ʷ) X01 ⟧₁ ≡ ⟦ M1 ⟧₁
  t7d0 = refl
  t7d2 : ⟦ (conj ʷ) X23 ⟧₁ ≡ ⟦ M3 ⟧₁
  t7d2 = refl
  t7d4 : ⟦ (conj ʷ) X45 ⟧₁ ≡ ⟦ M5 ⟧₁
  t7d4 = refl
  t7d6 : ⟦ (conj ʷ) X67 ⟧₁ ≡ ⟦ M7 ⟧₁
  t7d6 = refl

  -- (7d), x odd.
  t7d1 : ⟦ (conj ʷ) X12 ⟧₁ ≡ ⟦ X12 • K0123 ⟧₁
  t7d1 = refl
  t7d3 : ⟦ (conj ʷ) X34 ⟧₁ ≡ ⟦ X34 • K2345 ⟧₁
  t7d3 = refl
  t7d5 : ⟦ (conj ʷ) X56 ⟧₁ ≡ ⟦ X56 • K4567 ⟧₁
  t7d5 = refl

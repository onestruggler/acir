------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of Figure 7 in O(8, 𝔻), r93–r101 and r_K: each relation a lemma
-- typed by the relation it proves, decided by computing both sides'
-- matrices (Soundness dispatches to them; one module took 26 s).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Soundness.Figure7b where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using (Word)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; _≟ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)

open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Decide using (module Over)

open Over _≟ᴰ_ using (eqM-sound)

private
  variable
    k : ℕ

Goal₇ : {w v : Word (Gate (suc k))} → w ===₇ v → Set
Goal₇ {w = w} {v} _ = ⟦ w ⟧ ≡ ⟦ v ⟧

Goalᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → Set
Goalᴷ {w = w} {v} _ = ⟦ w ⟧ ≡ ⟦ v ⟧

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  s93 : Goal₇ (r93 {k})
  s93 = eqM-sound _ _ refl

  s94 : Goal₇ (r94 {k})
  s94 = eqM-sound _ _ refl

  s95 : Goal₇ (r95 {k})
  s95 = eqM-sound _ _ refl

  s96 : Goal₇ (r96 {k})
  s96 = eqM-sound _ _ refl

  s97 : Goal₇ (r97 {k})
  s97 = eqM-sound _ _ refl

  s98 : Goal₇ (r98 {k})
  s98 = eqM-sound _ _ refl

  s99 : Goal₇ (r99 {k})
  s99 = eqM-sound _ _ refl

  s100 : Goal₇ (r100 {k})
  s100 = eqM-sound _ _ refl

  s101 : Goal₇ (r101 {k})
  s101 = eqM-sound _ _ refl

  sK : Goalᴷ (rK {k})
  sK = eqM-sound _ _ refl

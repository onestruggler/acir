------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of Figure 7 in O(8, 𝔻), r83–r92: each relation a lemma
-- typed by the relation it proves, decided by computing both sides'
-- matrices (Soundness dispatches to them; one module took 26 s).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Soundness.Figure7a where

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

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  s83 : Goal₇ (r83 {k})
  s83 = eqM-sound _ _ refl

  s84 : Goal₇ (r84 {k})
  s84 = eqM-sound _ _ refl

  s85 : Goal₇ (r85 {k})
  s85 = eqM-sound _ _ refl

  s86 : Goal₇ (r86 {k})
  s86 = eqM-sound _ _ refl

  s87 : Goal₇ (r87 {k})
  s87 = eqM-sound _ _ refl

  s88 : Goal₇ (r88 {k})
  s88 = eqM-sound _ _ refl

  s89 : Goal₇ (r89 {k})
  s89 = eqM-sound _ _ refl

  s90 : Goal₇ (r90 {k})
  s90 = eqM-sound _ _ refl

  s91 : Goal₇ (r91 {k})
  s91 = eqM-sound _ _ refl

  s92 : Goal₇ (r92 {k})
  s92 = eqM-sound _ _ refl

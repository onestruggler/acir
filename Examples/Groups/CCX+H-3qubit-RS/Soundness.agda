------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness in O(8, 𝔻): every relation of Figure 4 (R₀), of Figure 7
-- (R₈₄) and r_K holds for the matrices, at every level.  Both sides
-- are closed words, compared by computing their matrices, each
-- comparison one boolean (Decide); Figure 7's, the costly ones, are
-- lemmas in Soundness/Figure7a and Figure7b.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Soundness where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; _≟ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)

open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Decide using (module Over)

import Examples.Groups.CCX+HH-3qubit-opus.Soundness.Figure7a as F7a
import Examples.Groups.CCX+HH-3qubit-opus.Soundness.Figure7b as F7b

open Over _≟ᴰ_ using (eqM-sound)

private
  variable
    k : ℕ

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  -- Figure 4.
  sound₀ : {w v : Word (Gate k)} → w ===₀ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  sound₀ r1 = eqM-sound _ _ refl
  sound₀ r2 = eqM-sound _ _ refl
  sound₀ r3 = eqM-sound _ _ refl
  sound₀ r4 = eqM-sound _ _ refl
  sound₀ r5 = eqM-sound _ _ refl
  sound₀ r6 = eqM-sound _ _ refl
  sound₀ r7 = eqM-sound _ _ refl
  sound₀ r8 = eqM-sound _ _ refl
  sound₀ r9 = eqM-sound _ _ refl
  sound₀ r10 = eqM-sound _ _ refl
  sound₀ r11 = eqM-sound _ _ refl
  sound₀ r12 = eqM-sound _ _ refl
  sound₀ r13 = eqM-sound _ _ refl
  sound₀ r14 = eqM-sound _ _ refl
  sound₀ r15 = eqM-sound _ _ refl
  sound₀ r16 = eqM-sound _ _ refl
  sound₀ r17 = eqM-sound _ _ refl
  sound₀ r18 = eqM-sound _ _ refl
  sound₀ r19 = eqM-sound _ _ refl
  sound₀ r20 = eqM-sound _ _ refl
  sound₀ r21 = eqM-sound _ _ refl
  sound₀ r22 = eqM-sound _ _ refl
  sound₀ r23 = eqM-sound _ _ refl
  sound₀ r24 = eqM-sound _ _ refl
  sound₀ r25 = eqM-sound _ _ refl
  sound₀ r26 = eqM-sound _ _ refl
  sound₀ r27 = eqM-sound _ _ refl
  sound₀ r28 = eqM-sound _ _ refl
  sound₀ r29 = eqM-sound _ _ refl
  sound₀ r30 = eqM-sound _ _ refl
  sound₀ r31 = eqM-sound _ _ refl
  sound₀ r32 = eqM-sound _ _ refl
  sound₀ r33 = eqM-sound _ _ refl
  sound₀ r34 = eqM-sound _ _ refl
  sound₀ r35 = eqM-sound _ _ refl
  sound₀ r36 = eqM-sound _ _ refl
  sound₀ r37 = eqM-sound _ _ refl
  sound₀ r38 = eqM-sound _ _ refl
  sound₀ r39 = eqM-sound _ _ refl
  sound₀ r40 = eqM-sound _ _ refl
  sound₀ r41 = eqM-sound _ _ refl
  sound₀ r42 = eqM-sound _ _ refl
  sound₀ r43 = eqM-sound _ _ refl
  sound₀ r44 = eqM-sound _ _ refl
  sound₀ r45 = eqM-sound _ _ refl
  sound₀ r46 = eqM-sound _ _ refl

  -- Figure 7.
  sound₇ : {w v : Word (Gate (suc k))} → w ===₇ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  sound₇ {k} r83 = F7a.s83 {k}
  sound₇ {k} r84 = F7a.s84 {k}
  sound₇ {k} r85 = F7a.s85 {k}
  sound₇ {k} r86 = F7a.s86 {k}
  sound₇ {k} r87 = F7a.s87 {k}
  sound₇ {k} r88 = F7a.s88 {k}
  sound₇ {k} r89 = F7a.s89 {k}
  sound₇ {k} r90 = F7a.s90 {k}
  sound₇ {k} r91 = F7a.s91 {k}
  sound₇ {k} r92 = F7a.s92 {k}
  sound₇ {k} r93 = F7b.s93 {k}
  sound₇ {k} r94 = F7b.s94 {k}
  sound₇ {k} r95 = F7b.s95 {k}
  sound₇ {k} r96 = F7b.s96 {k}
  sound₇ {k} r97 = F7b.s97 {k}
  sound₇ {k} r98 = F7b.s98 {k}
  sound₇ {k} r99 = F7b.s99 {k}
  sound₇ {k} r100 = F7b.s100 {k}
  sound₇ {k} r101 = F7b.s101 {k}

  -- r_K.
  soundᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  soundᴷ {k} rK = F7b.sK {k}

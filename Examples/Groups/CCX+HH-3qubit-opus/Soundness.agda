------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness in O(8, 𝔻): every relation of Figure 4 (R₀), of Figure 7
-- (R₈₄) and r_K holds for the matrices, at every level.  Both sides
-- are closed words, compared by computing their matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Soundness where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using (Word)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)

open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics

private
  variable
    k : ℕ

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  -- Figure 4.
  sound₀ : {w v : Word (Gate k)} → w ===₀ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  sound₀ r1 = refl
  sound₀ r2 = refl
  sound₀ r3 = refl
  sound₀ r4 = refl
  sound₀ r5 = refl
  sound₀ r6 = refl
  sound₀ r7 = refl
  sound₀ r8 = refl
  sound₀ r9 = refl
  sound₀ r10 = refl
  sound₀ r11 = refl
  sound₀ r12 = refl
  sound₀ r13 = refl
  sound₀ r14 = refl
  sound₀ r15 = refl
  sound₀ r16 = refl
  sound₀ r17 = refl
  sound₀ r18 = refl
  sound₀ r19 = refl
  sound₀ r20 = refl
  sound₀ r21 = refl
  sound₀ r22 = refl
  sound₀ r23 = refl
  sound₀ r24 = refl
  sound₀ r25 = refl
  sound₀ r26 = refl
  sound₀ r27 = refl
  sound₀ r28 = refl
  sound₀ r29 = refl
  sound₀ r30 = refl
  sound₀ r31 = refl
  sound₀ r32 = refl
  sound₀ r33 = refl
  sound₀ r34 = refl
  sound₀ r35 = refl
  sound₀ r36 = refl
  sound₀ r37 = refl
  sound₀ r38 = refl
  sound₀ r39 = refl
  sound₀ r40 = refl
  sound₀ r41 = refl
  sound₀ r42 = refl
  sound₀ r43 = refl
  sound₀ r44 = refl
  sound₀ r45 = refl
  sound₀ r46 = refl

  -- Figure 7.
  sound₇ : {w v : Word (Gate (suc k))} → w ===₇ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  sound₇ r83 = refl
  sound₇ r84 = refl
  sound₇ r85 = refl
  sound₇ r86 = refl
  sound₇ r87 = refl
  sound₇ r88 = refl
  sound₇ r89 = refl
  sound₇ r90 = refl
  sound₇ r91 = refl
  sound₇ r92 = refl
  sound₇ r93 = refl
  sound₇ r94 = refl
  sound₇ r95 = refl
  sound₇ r96 = refl
  sound₇ r97 = refl
  sound₇ r98 = refl
  sound₇ r99 = refl
  sound₇ r100 = refl
  sound₇ r101 = refl

  -- r_K.
  soundᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → ⟦ w ⟧ ≡ ⟦ v ⟧
  soundᴷ rK = refl

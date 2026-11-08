------------------------------------------------------------------------
-- Presentations of groups
--
-- A relation of Figure 4 or 7, or r_K, at one level is the same
-- relation one level up, so derivations lift: from Figure 4 at level 0
-- to R₁⁺, and from R₁⁺ to R₂⁺.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Lift where

open import Data.Nat.Base using (ℕ ; suc)

open import Word.Base using (Word)
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics

private
  variable
    k : ℕ

up₀ : {w v : Word (Gate k)} → w ===₀ v → ↑ʷ w ===₀ ↑ʷ v
up₀ r1 = r1
up₀ r2 = r2
up₀ r3 = r3
up₀ r4 = r4
up₀ r5 = r5
up₀ r6 = r6
up₀ r7 = r7
up₀ r8 = r8
up₀ r9 = r9
up₀ r10 = r10
up₀ r11 = r11
up₀ r12 = r12
up₀ r13 = r13
up₀ r14 = r14
up₀ r15 = r15
up₀ r16 = r16
up₀ r17 = r17
up₀ r18 = r18
up₀ r19 = r19
up₀ r20 = r20
up₀ r21 = r21
up₀ r22 = r22
up₀ r23 = r23
up₀ r24 = r24
up₀ r25 = r25
up₀ r26 = r26
up₀ r27 = r27
up₀ r28 = r28
up₀ r29 = r29
up₀ r30 = r30
up₀ r31 = r31
up₀ r32 = r32
up₀ r33 = r33
up₀ r34 = r34
up₀ r35 = r35
up₀ r36 = r36
up₀ r37 = r37
up₀ r38 = r38
up₀ r39 = r39
up₀ r40 = r40
up₀ r41 = r41
up₀ r42 = r42
up₀ r43 = r43
up₀ r44 = r44
up₀ r45 = r45
up₀ r46 = r46

up₇ : {w v : Word (Gate (suc k))} → w ===₇ v → ↑ʷ w ===₇ ↑ʷ v
up₇ r83 = r83
up₇ r84 = r84
up₇ r85 = r85
up₇ r86 = r86
up₇ r87 = r87
up₇ r88 = r88
up₇ r89 = r89
up₇ r90 = r90
up₇ r91 = r91
up₇ r92 = r92
up₇ r93 = r93
up₇ r94 = r94
up₇ r95 = r95
up₇ r96 = r96
up₇ r97 = r97
up₇ r98 = r98
up₇ r99 = r99
up₇ r100 = r100
up₇ r101 = r101

upᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → ↑ʷ w ===ᴷ ↑ʷ v
upᴷ rK = rK

-- Figure 4 at level 0 into R₁⁺.
lift₀₁ : {w v : Word Gᴰ} → PB._≈_ (_===₀_ {0}) w v → PB._≈_ _===₁⁺_ (↑ʷ w) (↑ʷ v)
lift₀₁ = GC.fʷ-cong
  where
  module GC = PP.GenCongruence (_===₀_ {0}) _===₁⁺_ up (λ a → PB.axiom (fig4 (up₀ a)))

-- R₁⁺ into R₂⁺.
lift₁₂ : {w v : Word G₁} → PB._≈_ _===₁⁺_ w v → PB._≈_ _===₂⁺_ (↑ʷ w) (↑ʷ v)
lift₁₂ = GC.fʷ-cong
  where
  wd : {w v : Word G₁} → w ===₁⁺ v → PB._≈_ _===₂⁺_ (↑ʷ w) (↑ʷ v)
  wd (fig4 a) = PB.axiom (fig4 (up₀ a))
  wd (fig7 a) = PB.axiom (fig7 (up₇ a))
  wd (rK a)   = PB.axiom (rK (upᴷ a))
  module GC = PP.GenCongruence _===₁⁺_ _===₂⁺_ up wd

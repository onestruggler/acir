{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00802 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00151 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00152 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00119 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00120 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00114 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00115 as L8

proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

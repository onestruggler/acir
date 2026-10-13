{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00731 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00117 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00077 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00078 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00079 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00073 as L6

proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2) • X12 ≈ X03 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

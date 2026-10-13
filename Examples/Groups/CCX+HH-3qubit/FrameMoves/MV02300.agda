{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02300 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00048 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00046 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00043 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00042 as L13

proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))) Eq.refl Eq.refl

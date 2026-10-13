{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02099 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00046 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00041 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00037 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00029 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00030 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00021 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00022 as L13

proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
proved = by-assoc-and (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))) Eq.refl Eq.refl

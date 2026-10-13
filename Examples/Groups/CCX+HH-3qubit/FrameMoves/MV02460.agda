{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02460 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00050 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00051 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L10

proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) • M7 ≈ M1 • p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
proved = by-assoc-and (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))) Eq.refl Eq.refl

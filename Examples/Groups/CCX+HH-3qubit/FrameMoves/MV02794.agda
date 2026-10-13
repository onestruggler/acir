{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02794 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00024 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00048 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00051 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00050 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00051 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00049 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00050 as L11

proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))) Eq.refl Eq.refl

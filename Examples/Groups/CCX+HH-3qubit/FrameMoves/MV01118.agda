{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01118 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00222 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00203 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00204 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00205 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00194 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00168 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00169 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00170 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00159 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00126 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00127 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00128 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00117 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00077 as L15
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00078 as L16

proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X04 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
proved = by-assoc-and (move-compose L16.proved (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))))))))) Eq.refl Eq.refl

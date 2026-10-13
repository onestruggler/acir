{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02152 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00259 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00282 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00300 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00309 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00368 as L9

proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02779 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00061 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00057 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00056 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00064 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00069 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00111 as L9

proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

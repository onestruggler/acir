{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01578 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00223 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00235 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00236 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00224 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00225 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00214 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00193 as L9

proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

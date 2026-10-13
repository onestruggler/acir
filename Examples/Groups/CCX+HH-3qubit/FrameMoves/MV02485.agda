{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02485 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00440 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00551 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00624 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00628 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00627 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00626 as L6

proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • K0567 ≈ K4567 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00254 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00276 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00292 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00350 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00387 as L6

proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

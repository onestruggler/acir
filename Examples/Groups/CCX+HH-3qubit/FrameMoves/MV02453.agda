{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02453 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00035 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00036 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00037 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 as L8

proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • M5 ≈ M0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

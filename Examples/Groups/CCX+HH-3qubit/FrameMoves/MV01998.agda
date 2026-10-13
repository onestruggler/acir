{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01998 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00033 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00030 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00025 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00022 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L8

proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

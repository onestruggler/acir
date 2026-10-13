{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01946 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00025 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00026 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00017 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00018 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L7

proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00196 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00197 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00187 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00161 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00162 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00152 as L7

proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X14 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02402 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00625 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00620 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00613 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00593 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00577 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00565 as L6

proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1347 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

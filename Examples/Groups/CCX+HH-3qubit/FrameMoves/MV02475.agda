{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02475 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00410 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00521 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00574 as L2

proved : p (s0 • s1 • s0) • K0357 ≈ K2357 • p (s0 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

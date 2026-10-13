{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02470 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L2

proved : p (s5 • s6 • s5) • M7 ≈ M5 • p (s5 • s6 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

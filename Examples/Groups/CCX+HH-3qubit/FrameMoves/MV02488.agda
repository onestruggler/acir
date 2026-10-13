{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02488 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00545 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00598 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00617 as L2

proved : p (s1 • s2 • s1) • K1467 ≈ K3467 • p (s1 • s2 • s1)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

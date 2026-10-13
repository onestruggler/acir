{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02977 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00147 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00153 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00180 as L2

proved : p (s1 • s2 • s3) • X23 ≈ X34 • p (s1 • s2 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

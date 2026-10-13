{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02523 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00338 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00358 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00371 as L2

proved : p (s3 • s4 • s3) • K0236 ≈ K0256 • p (s3 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

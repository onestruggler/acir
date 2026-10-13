{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02491 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00624 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00628 as L2

proved : p (s2 • s3 • s2) • K2567 ≈ K4567 • p (s2 • s3 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

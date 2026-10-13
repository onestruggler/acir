{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02895 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00106 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00111 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00145 as L3

proved : p (s0 • s1 • s2 • s3) • X12 ≈ X23 • p (s0 • s1 • s2 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

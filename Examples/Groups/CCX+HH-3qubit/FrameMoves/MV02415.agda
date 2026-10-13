{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02415 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00623 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00603 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00550 as L3

proved : p (s0 • s1 • s2 • s3) • K4567 ≈ K0567 • p (s0 • s1 • s2 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

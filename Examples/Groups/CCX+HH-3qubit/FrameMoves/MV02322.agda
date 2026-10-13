{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02322 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00248 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00254 as L5

proved : p (s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

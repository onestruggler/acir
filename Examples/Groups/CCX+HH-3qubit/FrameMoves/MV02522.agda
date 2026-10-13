{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02522 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00318 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00323 as L2

proved : p (s4 • s5 • s4) • K0147 ≈ K0167 • p (s4 • s5 • s4)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

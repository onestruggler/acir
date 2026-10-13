{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02243 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L1

proved : p (s5 • s4) • K0123 ≈ K0123 • p (s5 • s4)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

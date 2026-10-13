{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02550 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00446 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00452 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00458 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00462 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00461 as L4

proved : p (s4 • s5 • s6 • s5 • s4) • K1234 ≈ K1237 • p (s4 • s5 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

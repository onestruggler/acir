{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01845 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00042 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00043 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L4

proved : p (s2 • s1 • s0 • s5 • s4) • M4 ≈ M6 • p (s2 • s1 • s0 • s5 • s4)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01846 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00006 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 as L5

proved : p (s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M3 • p (s2 • s1 • s0 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02450 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00014 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 as L2

proved : p (s0 • s1 • s0) • M2 ≈ M0 • p (s0 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

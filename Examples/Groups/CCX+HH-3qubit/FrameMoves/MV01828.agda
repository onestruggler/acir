{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01828 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00028 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00029 as L1

proved : p (s1 • s0) • M4 ≈ M4 • p (s1 • s0)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

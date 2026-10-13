{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01854 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00028 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00029 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00030 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L3

proved : p (s3 • s2 • s1 • s0) • M4 ≈ M3 • p (s3 • s2 • s1 • s0)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

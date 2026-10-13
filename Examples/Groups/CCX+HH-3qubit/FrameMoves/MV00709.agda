{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00709 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00104 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00063 as L1

proved : p (s1 • s0) • X12 ≈ X01 • p (s1 • s0)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

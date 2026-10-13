{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00715 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00110 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00070 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00071 as L3

proved : p (s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s2 • s1 • s0 • s2)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

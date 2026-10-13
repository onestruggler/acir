{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00751 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00124 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00084 as L4

proved : p (s1 • s0 • s4 • s3 • s2) • X12 ≈ X05 • p (s1 • s0 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

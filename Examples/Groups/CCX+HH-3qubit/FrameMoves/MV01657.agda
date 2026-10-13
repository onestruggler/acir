{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01657 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00229 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00230 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00214 as L4

proved : p (s2 • s4 • s3 • s4 • s5) • X45 ≈ X46 • p (s2 • s4 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

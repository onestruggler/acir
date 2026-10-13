{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02498 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00309 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00370 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00407 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00425 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00424 as L4

proved : p (s1 • s2 • s3 • s2 • s1) • K0156 ≈ K0456 • p (s1 • s2 • s3 • s2 • s1)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

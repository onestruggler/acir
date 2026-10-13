{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02563 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L2

proved : p (s5 • s4 • s3) • X01 ≈ X01 • p (s5 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

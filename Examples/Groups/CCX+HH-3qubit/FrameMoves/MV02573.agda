{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02573 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L1

proved : p (s2 • s3) • M1 ≈ M1 • p (s2 • s3)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

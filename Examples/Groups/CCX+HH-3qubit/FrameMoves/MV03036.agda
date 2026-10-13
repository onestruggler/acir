{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03036 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00557 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00563 as L1

proved : p (s6 • s5) • K2345 ≈ K2347 • p (s6 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

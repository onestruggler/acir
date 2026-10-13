{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03035 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00507 as L1

proved : p (s6 • s5) • K1345 ≈ K1347 • p (s6 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

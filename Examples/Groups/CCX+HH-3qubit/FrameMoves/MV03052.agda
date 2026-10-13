{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03052 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00252 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00253 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00255 as L3

proved : p (s3 • s4 • s6 • s5) • K0124 ≈ K0125 • p (s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

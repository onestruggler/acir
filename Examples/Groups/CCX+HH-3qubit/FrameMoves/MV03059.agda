{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03059 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00505 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00517 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00535 as L3

proved : p (s2 • s3 • s4 • s5) • K1345 ≈ K1456 • p (s2 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

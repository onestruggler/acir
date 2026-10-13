{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02836 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00005 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00006 as L3

proved : p (s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))) Eq.refl Eq.refl

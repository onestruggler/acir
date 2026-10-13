{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02998 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00147 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00155 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00160 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00186 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00185 as L4

proved : p (s0 • s1 • s2 • s4 • s3) • X23 ≈ X35 • p (s0 • s1 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

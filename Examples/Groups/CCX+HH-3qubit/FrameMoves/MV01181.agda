{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01181 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00218 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00222 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00203 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00201 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00173 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00138 as L6

proved : p (s0 • s1 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s2 • s4 • s3 • s6 • s5)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

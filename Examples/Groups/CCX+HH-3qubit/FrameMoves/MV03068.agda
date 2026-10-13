{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03068 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00507 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00511 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00525 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00530 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00548 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00552 as L6

proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1567 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

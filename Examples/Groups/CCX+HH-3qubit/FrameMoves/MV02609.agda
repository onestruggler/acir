{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02609 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00011 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00012 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00013 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00011 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00012 as L7

proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

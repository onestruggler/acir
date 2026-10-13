{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02689 where

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
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00024 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L11

proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M5 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))) Eq.refl Eq.refl

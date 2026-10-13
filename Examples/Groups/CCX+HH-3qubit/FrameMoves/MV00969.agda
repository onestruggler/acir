{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00969 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00001 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00002 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 as L8

proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

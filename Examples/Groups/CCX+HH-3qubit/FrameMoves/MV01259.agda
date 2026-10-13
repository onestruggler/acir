{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01259 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00263 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00264 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00314 as L8

proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

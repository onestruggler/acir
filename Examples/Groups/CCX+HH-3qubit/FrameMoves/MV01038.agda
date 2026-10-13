{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01038 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00189 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00183 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00184 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00181 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00154 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00148 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00146 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00112 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00104 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00063 as L10

proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))) Eq.refl Eq.refl

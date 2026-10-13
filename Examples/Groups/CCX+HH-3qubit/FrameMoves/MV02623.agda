{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02623 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00061 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00057 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00056 as L5

proved : p (s1 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

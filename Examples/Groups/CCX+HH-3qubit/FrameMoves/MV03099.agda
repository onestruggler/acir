{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03099 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00557 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00563 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00566 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00578 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00582 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00598 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00617 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00616 as L7

proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3467 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

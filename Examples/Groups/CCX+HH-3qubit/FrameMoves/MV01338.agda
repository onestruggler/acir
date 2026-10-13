{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01338 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00248 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00263 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00264 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00314 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00376 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00413 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00428 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00539 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00592 as L15

proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
proved = by-assoc-and (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))))) Eq.refl Eq.refl

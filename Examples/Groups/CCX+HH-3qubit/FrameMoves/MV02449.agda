{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02449 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00625 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00620 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00615 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00609 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00588 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00572 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00562 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00556 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00499 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00466 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00451 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00445 as L12
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00326 as L13
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00270 as L14
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00250 as L15

proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0123 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L15.proved (move-compose L14.proved (move-compose L13.proved (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))))))) Eq.refl Eq.refl

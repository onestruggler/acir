{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00924 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00125 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00160 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00188 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00206 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00207 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00208 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00189 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00183 as L11
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00184 as L12

proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X34 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L12.proved (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))))) Eq.refl Eq.refl

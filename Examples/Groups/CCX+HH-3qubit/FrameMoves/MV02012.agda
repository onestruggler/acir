{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02012 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00038 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00030 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00022 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00014 as L7

proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

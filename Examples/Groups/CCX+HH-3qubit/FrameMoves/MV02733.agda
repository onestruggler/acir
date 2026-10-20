{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02733 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M3 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00011 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00010 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00021 as L6

proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

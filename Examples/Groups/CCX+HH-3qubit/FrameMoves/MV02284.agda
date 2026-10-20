{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02284 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00045 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00046 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00044 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00043 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00042 as L6

proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

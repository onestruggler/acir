{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02464 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00051 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as L8

proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) • M7 ≈ M2 • p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

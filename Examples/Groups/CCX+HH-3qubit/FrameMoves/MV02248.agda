{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02248 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00040 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00048 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00052 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L6

proved : p (s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s6 • s5 • s4 • s3 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

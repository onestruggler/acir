{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02700 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00133 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00132 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00165 as L5

proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s0 • s1 • s2 • s5 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00810 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00151 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00152 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00119 as L5

proved : p (s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X14 • p (s2 • s1 • s0 • s1 • s3 • s2)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

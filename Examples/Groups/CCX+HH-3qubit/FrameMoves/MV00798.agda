{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00798 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00151 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00152 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00119 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00120 as L6

proved : p (s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s3 • s2 • s1 • s0 • s1 • s3 • s2)
proved = by-assoc-and (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))) Eq.refl Eq.refl

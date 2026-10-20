{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02902 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00106 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00107 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00151 as L5

proved : p (s0 • s1 • s3 • s2 • s4 • s3) • X12 ≈ X24 • p (s0 • s1 • s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

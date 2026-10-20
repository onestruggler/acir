{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00719 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00110 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00070 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00071 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00065 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00066 as L5

proved : p (s4 • s3 • s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s4 • s3 • s2 • s1 • s0 • s2)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

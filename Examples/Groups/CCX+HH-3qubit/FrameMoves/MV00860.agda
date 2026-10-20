{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00860 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00153 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00179 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00180 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00181 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00154 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00148 as L8

proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X23 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

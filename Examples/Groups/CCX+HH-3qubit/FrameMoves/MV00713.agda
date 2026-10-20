{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00713 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00104 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00063 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00057 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00058 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00060 as L5

proved : p (s5 • s4 • s3 • s2 • s1 • s0) • X12 ≈ X01 • p (s5 • s4 • s3 • s2 • s1 • s0)
proved = by-assoc-and (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))) Eq.refl Eq.refl

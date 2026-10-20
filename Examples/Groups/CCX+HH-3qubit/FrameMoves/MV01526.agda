{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01526 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00229 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00230 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00217 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00208 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00189 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00180 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00179 as L9

proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

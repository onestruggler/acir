{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00745 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00124 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00084 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00085 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00086 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00087 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00081 as L8

proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X04 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))) Eq.refl Eq.refl

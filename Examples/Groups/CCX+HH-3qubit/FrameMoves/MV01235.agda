{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00210 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00215 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00196 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00197 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00187 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00161 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00162 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00152 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00119 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00120 as L9

proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X13 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
proved = by-assoc-and (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))) Eq.refl Eq.refl

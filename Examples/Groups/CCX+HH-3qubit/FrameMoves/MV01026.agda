{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01026 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00137 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00139 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00174 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00202 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00223 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00237 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00239 as L10
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00240 as L11

proved : p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L11.proved (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))))))) Eq.refl Eq.refl

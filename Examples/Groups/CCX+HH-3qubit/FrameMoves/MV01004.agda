{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01004 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00132 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00167 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00195 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 as L7
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00226 as L8
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00227 as L9
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00228 as L10

proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X56 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L10.proved (move-compose L9.proved (move-compose L8.proved (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))))))))) Eq.refl Eq.refl

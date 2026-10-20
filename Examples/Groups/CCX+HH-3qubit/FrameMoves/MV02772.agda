{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02772 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00121 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00126 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00127 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00125 as L4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00160 as L5
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00185 as L6
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00186 as L7

proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X13 ≈ X35 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L7.proved (move-compose L6.proved (move-compose L5.proved (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved)))))))) Eq.refl Eq.refl

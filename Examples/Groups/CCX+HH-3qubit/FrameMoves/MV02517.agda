{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02517 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; K0157 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00264 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00316 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00315 as L4

proved : p (s2 • s3 • s4 • s3 • s2) • K0127 ≈ K0157 • p (s2 • s3 • s4 • s3 • s2)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

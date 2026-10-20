{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02520 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K0157 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00306 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00316 as L2

proved : p (s3 • s4 • s3) • K0137 ≈ K0157 • p (s3 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00737 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00117 as L2

proved : p (s0 • s3 • s2) • X12 ≈ X04 • p (s0 • s3 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

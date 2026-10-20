{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00727 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00110 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00070 as L2

proved : p (s1 • s0 • s2) • X12 ≈ X03 • p (s1 • s0 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

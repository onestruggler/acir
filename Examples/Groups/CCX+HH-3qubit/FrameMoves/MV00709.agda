{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00709 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00104 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00063 as L1

proved : p (s1 • s0) • X12 ≈ X01 • p (s1 • s0)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

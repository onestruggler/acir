{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02478 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; K2457 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00428 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00539 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00590 as L2

proved : p (s0 • s1 • s0) • K0457 ≈ K2457 • p (s0 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

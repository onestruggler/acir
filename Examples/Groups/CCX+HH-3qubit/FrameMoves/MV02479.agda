{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02479 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; K2467 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00434 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00545 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00596 as L2

proved : p (s0 • s1 • s0) • K0467 ≈ K2467 • p (s0 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

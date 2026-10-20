{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02548 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; K0347 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00390 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00397 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00402 as L2

proved : p (s5 • s6 • s5) • K0345 ≈ K0347 • p (s5 • s6 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

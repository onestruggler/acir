{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02544 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0236 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00327 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00334 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00339 as L2

proved : p (s4 • s5 • s4) • K0234 ≈ K0236 • p (s4 • s5 • s4)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02526 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; K0267 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00365 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00379 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00385 as L2

proved : p (s4 • s5 • s4) • K0247 ≈ K0267 • p (s4 • s5 • s4)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

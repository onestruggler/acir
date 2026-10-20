{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02538 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0127 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00263 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00267 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00266 as L4

proved : p (s4 • s5 • s6 • s5 • s4) • K0124 ≈ K0127 • p (s4 • s5 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

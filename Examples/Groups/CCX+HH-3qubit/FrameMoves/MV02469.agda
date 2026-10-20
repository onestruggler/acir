{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02469 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00053 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as L4

proved : p (s4 • s5 • s6 • s5 • s4) • M7 ≈ M4 • p (s4 • s5 • s6 • s5 • s4)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

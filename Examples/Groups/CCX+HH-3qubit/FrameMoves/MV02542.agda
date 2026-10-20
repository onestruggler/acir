{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02542 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K0137 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00278 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00285 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00290 as L2

proved : p (s5 • s6 • s5) • K0135 ≈ K0137 • p (s5 • s6 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

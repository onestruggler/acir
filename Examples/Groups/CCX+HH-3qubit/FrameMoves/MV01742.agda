{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01742 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00248 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as L2

proved : p (s4 • s6 • s5) • K0123 ≈ K0123 • p (s4 • s6 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

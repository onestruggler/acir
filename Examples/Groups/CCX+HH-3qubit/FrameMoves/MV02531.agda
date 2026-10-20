{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02531 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; K1267 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00478 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00490 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00495 as L2

proved : p (s4 • s5 • s4) • K1247 ≈ K1267 • p (s4 • s5 • s4)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

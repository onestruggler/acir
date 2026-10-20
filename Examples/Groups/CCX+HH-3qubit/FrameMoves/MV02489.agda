{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02489 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; K3567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00551 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00622 as L2

proved : p (s1 • s2 • s1) • K1567 ≈ K3567 • p (s1 • s2 • s1)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

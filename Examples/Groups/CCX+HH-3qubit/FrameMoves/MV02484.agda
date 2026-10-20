{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02484 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; K3567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00440 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00551 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00622 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00621 as L4

proved : p (s0 • s1 • s2 • s1 • s0) • K0567 ≈ K3567 • p (s0 • s1 • s2 • s1 • s0)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02416 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00625 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00618 as L2
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00597 as L3
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00544 as L4

proved : p (s0 • s1 • s2 • s4 • s3) • K4567 ≈ K0467 • p (s0 • s1 • s2 • s4 • s3)
proved = by-assoc-and (move-compose L4.proved (move-compose L3.proved (move-compose L2.proved (move-compose L1.proved (L0.proved))))) Eq.refl Eq.refl

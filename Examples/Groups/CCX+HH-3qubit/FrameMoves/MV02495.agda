{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02495 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; K0356 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00309 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00370 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00405 as L2

proved : p (s1 • s2 • s1) • K0156 ≈ K0356 • p (s1 • s2 • s1)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

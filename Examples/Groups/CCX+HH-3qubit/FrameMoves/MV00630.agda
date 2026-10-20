{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M3 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00008 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 as L2

proved : p (s2 • s1 • s0) • M0 ≈ M3 • p (s2 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02476 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; K2367 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00417 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00528 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00580 as L2

proved : p (s0 • s1 • s0) • K0367 ≈ K2367 • p (s0 • s1 • s0)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

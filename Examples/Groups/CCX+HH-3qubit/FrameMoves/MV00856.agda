{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00856 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s0 ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00111 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00145 as L2

proved : p (s0 • s1 • s2) • X12 ≈ X23 • p (s0 • s1 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

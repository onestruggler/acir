{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00854 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s1 ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00105 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00111 as L1

proved : p (s1 • s2) • X12 ≈ X23 • p (s1 • s2)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

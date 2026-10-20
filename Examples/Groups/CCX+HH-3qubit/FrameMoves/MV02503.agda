{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02503 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; K0457 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00376 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00413 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00430 as L2

proved : p (s2 • s3 • s2) • K0257 ≈ K0457 • p (s2 • s3 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

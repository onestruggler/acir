{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02502 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; K0456 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00370 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00407 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00425 as L2

proved : p (s2 • s3 • s2) • K0256 ≈ K0456 • p (s2 • s3 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

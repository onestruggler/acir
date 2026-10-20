{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00251 as L1

proved : p (s4 • s3) • K0123 ≈ K0125 • p (s4 • s3)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02529 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; K1257 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00460 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00478 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00488 as L2

proved : p (s3 • s4 • s3) • K1237 ≈ K1257 • p (s3 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

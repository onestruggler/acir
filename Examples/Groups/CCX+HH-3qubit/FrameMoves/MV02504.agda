{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02504 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; K0467 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s2 ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00383 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00420 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00436 as L2

proved : p (s2 • s3 • s2) • K0267 ≈ K0467 • p (s2 • s3 • s2)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

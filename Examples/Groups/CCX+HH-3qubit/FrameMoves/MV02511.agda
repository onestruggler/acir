{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02511 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; K1567 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00530 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00548 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00553 as L2

proved : p (s3 • s4 • s3) • K1367 ≈ K1567 • p (s3 • s4 • s3)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

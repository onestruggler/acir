{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03047 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K1456 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s3 ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00505 as L1
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00517 as L2

proved : p (s3 • s4 • s5) • K1345 ≈ K1456 • p (s3 • s4 • s5)
proved = by-assoc-and (move-compose L2.proved (move-compose L1.proved (L0.proved))) Eq.refl Eq.refl

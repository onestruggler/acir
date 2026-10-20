{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03038 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K1356 ; _•_ ; _≈_ ; by-assoc-and ; move-compose ; p ; s4 ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as L0
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00505 as L1

proved : p (s4 • s5) • K1345 ≈ K1356 • p (s4 • s5)
proved = by-assoc-and (move-compose L1.proved (L0.proved)) Eq.refl Eq.refl

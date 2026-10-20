{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij14567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; K4567 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02490 as Move

proved : X14 • K1567 ≈ K4567 • X14
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0126 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02537 as Move

proved : X46 • K0124 ≈ K0126 • X46
proved = by-assoc-and Move.proved Eq.refl Eq.refl

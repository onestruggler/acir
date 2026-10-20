{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; K0137 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00285 as Move

proved : X67 • K0136 ≈ K0137 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00327 as Move

proved : X45 • K0234 ≈ K0235 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

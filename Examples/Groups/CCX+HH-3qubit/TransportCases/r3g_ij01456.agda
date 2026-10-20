{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; K0146 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00295 as Move

proved : X56 • K0145 ≈ K0146 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

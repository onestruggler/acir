{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K0126 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00257 as Move

proved : X56 • K0125 ≈ K0126 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

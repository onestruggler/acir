{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij02457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; K0457 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02503 as Move

proved : X24 • K0257 ≈ K0457 • X24
proved = by-assoc-and Move.proved Eq.refl Eq.refl

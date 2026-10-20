{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; K0457 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02499 as Move

proved : X14 • K0157 ≈ K0457 • X14
proved = by-assoc-and Move.proved Eq.refl Eq.refl

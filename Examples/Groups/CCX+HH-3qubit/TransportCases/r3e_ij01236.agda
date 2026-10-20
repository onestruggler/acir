{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; K0236 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00280 as Move

proved : X12 • K0136 ≈ K0236 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

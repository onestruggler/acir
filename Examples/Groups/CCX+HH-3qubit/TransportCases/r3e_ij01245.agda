{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; K0245 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00292 as Move

proved : X12 • K0145 ≈ K0245 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

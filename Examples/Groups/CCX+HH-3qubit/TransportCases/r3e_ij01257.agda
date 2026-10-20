{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; K0257 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00314 as Move

proved : X12 • K0157 ≈ K0257 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

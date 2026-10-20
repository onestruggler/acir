{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij12345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K2345 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00498 as Move

proved : X12 • K1345 ≈ K2345 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

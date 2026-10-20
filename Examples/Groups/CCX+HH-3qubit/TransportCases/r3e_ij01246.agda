{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; K0246 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00297 as Move

proved : X12 • K0146 ≈ K0246 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

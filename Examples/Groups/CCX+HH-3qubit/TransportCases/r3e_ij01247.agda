{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; K0247 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00303 as Move

proved : X12 • K0147 ≈ K0247 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

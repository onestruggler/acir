{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij12347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; K2347 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00509 as Move

proved : X12 • K1347 ≈ K2347 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

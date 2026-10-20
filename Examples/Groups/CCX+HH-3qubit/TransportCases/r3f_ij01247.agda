{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; K0147 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02515 as Move

proved : X24 • K0127 ≈ K0147 • X24
proved = by-assoc-and Move.proved Eq.refl Eq.refl

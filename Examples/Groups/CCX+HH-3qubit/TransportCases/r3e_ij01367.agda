{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K0367 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02497 as Move

proved : X13 • K0167 ≈ K0367 • X13
proved = by-assoc-and Move.proved Eq.refl Eq.refl

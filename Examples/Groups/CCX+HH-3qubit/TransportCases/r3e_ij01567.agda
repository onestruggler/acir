{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K0567 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02501 as Move

proved : X15 • K0167 ≈ K0567 • X15
proved = by-assoc-and Move.proved Eq.refl Eq.refl

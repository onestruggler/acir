{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij01567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; K1567 ; X01 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00440 as Move

proved : X01 • K0567 ≈ K1567 • X01
proved = by-assoc-and Move.proved Eq.refl Eq.refl

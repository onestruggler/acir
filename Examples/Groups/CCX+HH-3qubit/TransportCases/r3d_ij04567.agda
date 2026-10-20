{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij04567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; K4567 ; X04 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02485 as Move

proved : X04 • K0567 ≈ K4567 • X04
proved = by-assoc-and Move.proved Eq.refl Eq.refl

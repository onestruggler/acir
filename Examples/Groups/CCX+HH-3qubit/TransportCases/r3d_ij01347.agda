{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij01347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; K1347 ; X01 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00398 as Move

proved : X01 • K0347 ≈ K1347 • X01
proved = by-assoc-and Move.proved Eq.refl Eq.refl

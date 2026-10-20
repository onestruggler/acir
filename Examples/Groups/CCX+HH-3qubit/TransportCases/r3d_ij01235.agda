{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij01235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K1235 ; X01 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00330 as Move

proved : X01 • K0235 ≈ K1235 • X01
proved = by-assoc-and Move.proved Eq.refl Eq.refl

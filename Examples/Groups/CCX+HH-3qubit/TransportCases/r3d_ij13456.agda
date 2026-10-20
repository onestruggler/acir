{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij13456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; K3456 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02486 as Move

proved : X13 • K1456 ≈ K3456 • X13
proved = by-assoc-and Move.proved Eq.refl Eq.refl

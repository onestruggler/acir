{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij02346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; K2346 ; X02 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02472 as Move

proved : X02 • K0346 ≈ K2346 • X02
proved = by-assoc-and Move.proved Eq.refl Eq.refl

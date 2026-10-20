{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij02367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; K2367 ; X02 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02476 as Move

proved : X02 • K0367 ≈ K2367 • X02
proved = by-assoc-and Move.proved Eq.refl Eq.refl

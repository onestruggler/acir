{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij03467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; K0367 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02527 as Move

proved : X46 • K0347 ≈ K0367 • X46
proved = by-assoc-and Move.proved Eq.refl Eq.refl

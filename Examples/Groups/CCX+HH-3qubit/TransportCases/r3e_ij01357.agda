{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; K0357 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02496 as Move

proved : X13 • K0157 ≈ K0357 • X13
proved = by-assoc-and Move.proved Eq.refl Eq.refl

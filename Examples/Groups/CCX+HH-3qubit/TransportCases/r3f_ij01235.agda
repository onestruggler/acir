{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K0135 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00254 as Move

proved : X23 • K0125 ≈ K0135 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

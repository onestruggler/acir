{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K0167 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02521 as Move

proved : X36 • K0137 ≈ K0167 • X36
proved = by-assoc-and Move.proved Eq.refl Eq.refl

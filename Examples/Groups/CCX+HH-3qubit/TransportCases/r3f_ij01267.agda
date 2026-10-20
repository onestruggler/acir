{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; K0167 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02518 as Move

proved : X26 • K0127 ≈ K0167 • X26
proved = by-assoc-and Move.proved Eq.refl Eq.refl

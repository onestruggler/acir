{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; K0157 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02517 as Move

proved : X25 • K0127 ≈ K0157 • X25
proved = by-assoc-and Move.proved Eq.refl Eq.refl

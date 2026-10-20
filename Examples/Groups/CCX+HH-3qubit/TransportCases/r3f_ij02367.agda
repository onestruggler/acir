{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij02367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K0267 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02525 as Move

proved : X36 • K0237 ≈ K0267 • X36
proved = by-assoc-and Move.proved Eq.refl Eq.refl

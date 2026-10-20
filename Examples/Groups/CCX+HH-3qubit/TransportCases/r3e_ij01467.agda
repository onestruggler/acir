{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K0467 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02500 as Move

proved : X14 • K0167 ≈ K0467 • X14
proved = by-assoc-and Move.proved Eq.refl Eq.refl

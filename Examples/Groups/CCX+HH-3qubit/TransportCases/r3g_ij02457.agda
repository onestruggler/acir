{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K0247 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02547 as Move

proved : X57 • K0245 ≈ K0247 • X57
proved = by-assoc-and Move.proved Eq.refl Eq.refl

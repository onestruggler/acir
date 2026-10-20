{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K0127 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02539 as Move

proved : X57 • K0125 ≈ K0127 • X57
proved = by-assoc-and Move.proved Eq.refl Eq.refl

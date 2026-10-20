{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; K0147 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02543 as Move

proved : X57 • K0145 ≈ K0147 • X57
proved = by-assoc-and Move.proved Eq.refl Eq.refl

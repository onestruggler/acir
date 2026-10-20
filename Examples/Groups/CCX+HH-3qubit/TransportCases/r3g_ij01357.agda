{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K0137 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02542 as Move

proved : X57 • K0135 ≈ K0137 • X57
proved = by-assoc-and Move.proved Eq.refl Eq.refl

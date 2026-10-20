{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij12346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; K1236 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02549 as Move

proved : X46 • K1234 ≈ K1236 • X46
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij12356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; K1236 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00452 as Move

proved : X56 • K1235 ≈ K1236 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

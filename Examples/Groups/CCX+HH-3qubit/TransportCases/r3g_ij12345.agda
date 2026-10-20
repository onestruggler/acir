{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij12345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; K1235 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00446 as Move

proved : X45 • K1234 ≈ K1235 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

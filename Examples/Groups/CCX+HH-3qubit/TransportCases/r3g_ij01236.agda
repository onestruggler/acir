{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0126 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02535 as Move

proved : X36 • K0123 ≈ K0126 • X36
proved = by-assoc-and Move.proved Eq.refl Eq.refl

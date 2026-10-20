{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0127 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02536 as Move

proved : X37 • K0123 ≈ K0127 • X37
proved = by-assoc-and Move.proved Eq.refl Eq.refl

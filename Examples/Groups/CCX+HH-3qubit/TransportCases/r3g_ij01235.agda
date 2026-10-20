{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02534 as Move

proved : X35 • K0123 ≈ K0125 • X35
proved = by-assoc-and Move.proved Eq.refl Eq.refl

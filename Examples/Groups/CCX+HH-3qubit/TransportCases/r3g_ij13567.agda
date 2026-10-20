{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij13567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; K1357 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00519 as Move

proved : X67 • K1356 ≈ K1357 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

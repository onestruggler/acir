{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij03456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; K0346 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00390 as Move

proved : X56 • K0345 ≈ K0346 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

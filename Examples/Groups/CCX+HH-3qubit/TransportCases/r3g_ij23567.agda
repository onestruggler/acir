{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij23567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; K2357 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00573 as Move

proved : X67 • K2356 ≈ K2357 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

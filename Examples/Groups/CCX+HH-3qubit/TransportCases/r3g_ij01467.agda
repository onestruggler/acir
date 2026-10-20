{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; K0147 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00302 as Move

proved : X67 • K0146 ≈ K0147 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

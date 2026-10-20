{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K0147 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00288 as Move

proved : X34 • K0137 ≈ K0147 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

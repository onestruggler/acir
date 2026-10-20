{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K0145 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00276 as Move

proved : X34 • K0135 ≈ K0145 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

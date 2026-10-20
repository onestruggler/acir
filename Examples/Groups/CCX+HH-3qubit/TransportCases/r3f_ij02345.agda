{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij02345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K0245 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00332 as Move

proved : X34 • K0235 ≈ K0245 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

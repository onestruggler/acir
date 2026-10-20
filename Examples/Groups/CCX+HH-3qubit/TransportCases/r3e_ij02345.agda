{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij02345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K0345 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00350 as Move

proved : X23 • K0245 ≈ K0345 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

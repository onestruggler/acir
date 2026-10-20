{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; K0136 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00259 as Move

proved : X23 • K0126 ≈ K0136 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

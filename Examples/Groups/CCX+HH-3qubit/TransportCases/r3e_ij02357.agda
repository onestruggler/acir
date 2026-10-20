{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij02357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; K0357 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00376 as Move

proved : X23 • K0257 ≈ K0357 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

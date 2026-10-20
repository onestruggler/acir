{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij12457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; K1457 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02508 as Move

proved : X24 • K1257 ≈ K1457 • X24
proved = by-assoc-and Move.proved Eq.refl Eq.refl

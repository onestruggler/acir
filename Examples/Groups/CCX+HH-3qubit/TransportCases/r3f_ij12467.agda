{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij12467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; K1267 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02531 as Move

proved : X46 • K1247 ≈ K1267 • X46
proved = by-assoc-and Move.proved Eq.refl Eq.refl

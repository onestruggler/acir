{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij12346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; K1346 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00470 as Move

proved : X23 • K1246 ≈ K1346 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

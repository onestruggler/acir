{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij12347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; K1347 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00476 as Move

proved : X23 • K1247 ≈ K1347 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij12367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; K1267 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02530 as Move

proved : X36 • K1237 ≈ K1267 • X36
proved = by-assoc-and Move.proved Eq.refl Eq.refl

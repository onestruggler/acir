{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij12567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; K1567 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02510 as Move

proved : X25 • K1267 ≈ K1567 • X25
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0237 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02545 as Move

proved : X47 • K0234 ≈ K0237 • X47
proved = by-assoc-and Move.proved Eq.refl Eq.refl

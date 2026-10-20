{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; K0257 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00373 as Move

proved : X67 • K0256 ≈ K0257 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

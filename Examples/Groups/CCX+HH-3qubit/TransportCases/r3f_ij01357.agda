{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij01357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K0157 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02520 as Move

proved : X35 • K0137 ≈ K0157 • X35
proved = by-assoc-and Move.proved Eq.refl Eq.refl

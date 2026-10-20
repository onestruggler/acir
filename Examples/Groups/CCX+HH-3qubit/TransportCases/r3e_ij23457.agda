{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij23457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; K2457 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00576 as Move

proved : X34 • K2357 ≈ K2457 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij03457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; K0457 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00413 as Move

proved : X34 • K0357 ≈ K0457 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

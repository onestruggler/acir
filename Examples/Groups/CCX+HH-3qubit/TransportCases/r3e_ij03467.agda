{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij03467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; K0467 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00420 as Move

proved : X34 • K0367 ≈ K0467 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

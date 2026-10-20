{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij04567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; K0467 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00432 as Move

proved : X56 • K0457 ≈ K0467 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

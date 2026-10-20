{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij24567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; K2567 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00600 as Move

proved : X45 • K2467 ≈ K2567 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

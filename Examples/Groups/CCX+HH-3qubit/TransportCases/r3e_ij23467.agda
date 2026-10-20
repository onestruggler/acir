{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij23467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; K2467 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00582 as Move

proved : X34 • K2367 ≈ K2467 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

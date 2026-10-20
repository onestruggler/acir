{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij36 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M6 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02466 as Move

proved : X36 • M6 ≈ M3 • X36
proved = by-assoc-and Move.proved Eq.refl Eq.refl

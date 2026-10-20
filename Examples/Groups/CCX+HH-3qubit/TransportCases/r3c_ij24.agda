{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij24 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M4 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02461 as Move

proved : X24 • M4 ≈ M2 • X24
proved = by-assoc-and Move.proved Eq.refl Eq.refl

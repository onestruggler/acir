{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij07 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M7 ; X07 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02455 as Move

proved : X07 • M7 ≈ M0 • X07
proved = by-assoc-and Move.proved Eq.refl Eq.refl

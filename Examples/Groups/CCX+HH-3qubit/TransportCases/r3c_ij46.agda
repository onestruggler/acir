{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij46 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M6 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02468 as Move

proved : X46 • M6 ≈ M4 • X46
proved = by-assoc-and Move.proved Eq.refl Eq.refl

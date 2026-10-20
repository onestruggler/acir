{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij14 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M4 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02457 as Move

proved : X14 • M4 ≈ M1 • X14
proved = by-assoc-and Move.proved Eq.refl Eq.refl

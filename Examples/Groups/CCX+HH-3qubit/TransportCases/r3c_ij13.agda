{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij13 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M3 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02456 as Move

proved : X13 • M3 ≈ M1 • X13
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij15 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M5 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02458 as Move

proved : X15 • M5 ≈ M1 • X15
proved = by-assoc-and Move.proved Eq.refl Eq.refl

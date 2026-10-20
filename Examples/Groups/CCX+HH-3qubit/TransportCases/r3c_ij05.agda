{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij05 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M5 ; X05 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02453 as Move

proved : X05 • M5 ≈ M0 • X05
proved = by-assoc-and Move.proved Eq.refl Eq.refl

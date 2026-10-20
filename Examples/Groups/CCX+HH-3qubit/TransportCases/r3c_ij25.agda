{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij25 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M5 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02462 as Move

proved : X25 • M5 ≈ M2 • X25
proved = by-assoc-and Move.proved Eq.refl Eq.refl

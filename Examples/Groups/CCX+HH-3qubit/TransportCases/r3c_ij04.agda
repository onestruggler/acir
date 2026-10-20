{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; X04 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02452 as Move

proved : X04 • M4 ≈ M0 • X04
proved = by-assoc-and Move.proved Eq.refl Eq.refl

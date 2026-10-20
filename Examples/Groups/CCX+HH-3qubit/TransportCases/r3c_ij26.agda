{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij26 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M6 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02463 as Move

proved : X26 • M6 ≈ M2 • X26
proved = by-assoc-and Move.proved Eq.refl Eq.refl

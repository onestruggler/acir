{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij37 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M7 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02467 as Move

proved : X37 • M7 ≈ M3 • X37
proved = by-assoc-and Move.proved Eq.refl Eq.refl

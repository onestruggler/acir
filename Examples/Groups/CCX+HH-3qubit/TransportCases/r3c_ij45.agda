{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij45 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M5 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00039 as Move

proved : X45 • M5 ≈ M4 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

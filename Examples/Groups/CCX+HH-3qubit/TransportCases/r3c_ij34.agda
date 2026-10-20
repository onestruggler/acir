{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij34 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M4 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00031 as Move

proved : X34 • M4 ≈ M3 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

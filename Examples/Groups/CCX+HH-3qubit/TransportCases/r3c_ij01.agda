{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; X01 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 as Move

proved : X01 • M1 ≈ M0 • X01
proved = by-assoc-and Move.proved Eq.refl Eq.refl

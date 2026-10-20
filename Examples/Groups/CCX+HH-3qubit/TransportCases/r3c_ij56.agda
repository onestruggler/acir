{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij56 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; M6 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00047 as Move

proved : X56 • M6 ≈ M5 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

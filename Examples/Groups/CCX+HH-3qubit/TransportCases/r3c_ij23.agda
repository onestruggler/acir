{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij23 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M3 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00023 as Move

proved : X23 • M3 ≈ M2 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

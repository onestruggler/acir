{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij06 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M6 ; X06 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02454 as Move

proved : X06 • M6 ≈ M0 • X06
proved = by-assoc-and Move.proved Eq.refl Eq.refl

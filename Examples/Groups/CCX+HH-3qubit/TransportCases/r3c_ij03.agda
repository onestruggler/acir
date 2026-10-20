{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij03 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M3 ; X03 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02451 as Move

proved : X03 • M3 ≈ M0 • X03
proved = by-assoc-and Move.proved Eq.refl Eq.refl

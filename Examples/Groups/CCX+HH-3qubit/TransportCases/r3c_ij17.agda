{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij17 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M7 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02460 as Move

proved : X17 • M7 ≈ M1 • X17
proved = by-assoc-and Move.proved Eq.refl Eq.refl

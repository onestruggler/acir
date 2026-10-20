{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij47 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M7 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02469 as Move

proved : X47 • M7 ≈ M4 • X47
proved = by-assoc-and Move.proved Eq.refl Eq.refl

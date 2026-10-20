{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij57 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; M7 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02470 as Move

proved : X57 • M7 ≈ M5 • X57
proved = by-assoc-and Move.proved Eq.refl Eq.refl

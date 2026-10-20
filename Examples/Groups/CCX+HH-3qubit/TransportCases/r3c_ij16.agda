{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij16 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M6 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02459 as Move

proved : X16 • M6 ≈ M1 • X16
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij27 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M7 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02464 as Move

proved : X27 • M7 ≈ M2 • X27
proved = by-assoc-and Move.proved Eq.refl Eq.refl

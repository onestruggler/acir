{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M2 ; X02 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02450 as Move

proved : X02 • M2 ≈ M0 • X02
proved = by-assoc-and Move.proved Eq.refl Eq.refl

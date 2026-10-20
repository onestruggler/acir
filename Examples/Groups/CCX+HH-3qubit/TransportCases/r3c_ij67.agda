{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij67 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; M7 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00055 as Move

proved : X67 • M7 ≈ M6 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

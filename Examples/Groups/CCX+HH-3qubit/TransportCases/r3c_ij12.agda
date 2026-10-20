{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3c_ij12 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00015 as Move

proved : X12 • M2 ≈ M1 • X12
proved = by-assoc-and Move.proved Eq.refl Eq.refl

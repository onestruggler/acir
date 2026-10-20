{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij01456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; K0456 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02498 as Move

proved : X14 • K0156 ≈ K0456 • X14
proved = by-assoc-and Move.proved Eq.refl Eq.refl

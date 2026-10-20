{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij02456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; K2456 ; X02 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02477 as Move

proved : X02 • K0456 ≈ K2456 • X02
proved = by-assoc-and Move.proved Eq.refl Eq.refl

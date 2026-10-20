{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij03457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; K3457 ; X03 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02482 as Move

proved : X03 • K0457 ≈ K3457 • X03
proved = by-assoc-and Move.proved Eq.refl Eq.refl

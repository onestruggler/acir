{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij34567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; K4567 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00624 as Move

proved : X34 • K3567 ≈ K4567 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

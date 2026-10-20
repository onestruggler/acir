{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij23567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; K3567 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00604 as Move

proved : X23 • K2567 ≈ K3567 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

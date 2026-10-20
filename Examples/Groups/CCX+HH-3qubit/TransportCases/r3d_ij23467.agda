{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3d_ij23467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; K3467 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00598 as Move

proved : X23 • K2467 ≈ K3467 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

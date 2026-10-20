{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij34567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; K3567 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00619 as Move

proved : X45 • K3467 ≈ K3567 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij34567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; K3467 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00614 as Move

proved : X56 • K3457 ≈ K3467 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

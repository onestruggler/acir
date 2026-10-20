{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij34567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; K3457 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00610 as Move

proved : X67 • K3456 ≈ K3457 • X67
proved = by-assoc-and Move.proved Eq.refl Eq.refl

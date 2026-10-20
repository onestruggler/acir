{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij02456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; K0256 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00358 as Move

proved : X45 • K0246 ≈ K0256 • X45
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij02356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; K0356 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00370 as Move

proved : X23 • K0256 ≈ K0356 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij02347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; K0347 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00363 as Move

proved : X23 • K0247 ≈ K0347 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij02347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K0247 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00344 as Move

proved : X34 • K0237 ≈ K0247 • X34
proved = by-assoc-and Move.proved Eq.refl Eq.refl

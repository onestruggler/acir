{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij13567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; K1367 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00525 as Move

proved : X56 • K1357 ≈ K1367 • X56
proved = by-assoc-and Move.proved Eq.refl Eq.refl

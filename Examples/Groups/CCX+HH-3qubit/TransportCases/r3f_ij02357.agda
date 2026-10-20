{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij02357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K0257 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02524 as Move

proved : X35 • K0237 ≈ K0257 • X35
proved = by-assoc-and Move.proved Eq.refl Eq.refl

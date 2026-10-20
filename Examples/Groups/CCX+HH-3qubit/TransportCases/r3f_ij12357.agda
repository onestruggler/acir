{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3f_ij12357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; K1257 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02529 as Move

proved : X35 • K1237 ≈ K1257 • X35
proved = by-assoc-and Move.proved Eq.refl Eq.refl

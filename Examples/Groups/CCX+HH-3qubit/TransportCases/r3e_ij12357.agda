{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3e_ij12357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; K1357 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00487 as Move

proved : X23 • K1257 ≈ K1357 • X23
proved = by-assoc-and Move.proved Eq.refl Eq.refl

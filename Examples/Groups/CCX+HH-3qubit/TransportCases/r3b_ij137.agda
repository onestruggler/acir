{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X17 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01357 as E

proved : X37 • X13 ≈ X17 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

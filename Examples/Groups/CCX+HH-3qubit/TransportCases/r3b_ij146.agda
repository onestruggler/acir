{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X16 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01358 as E

proved : X46 • X14 ≈ X16 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

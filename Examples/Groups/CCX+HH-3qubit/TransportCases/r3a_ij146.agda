{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X16 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01321 as E

proved : X14 • X16 ≈ X46 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

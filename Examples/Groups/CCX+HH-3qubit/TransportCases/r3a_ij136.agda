{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X16 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01318 as E

proved : X13 • X16 ≈ X36 • X13
proved = by-assoc-and E.proved Eq.refl Eq.refl

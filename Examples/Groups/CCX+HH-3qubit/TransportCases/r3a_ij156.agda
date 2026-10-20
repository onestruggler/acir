{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X16 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01323 as E

proved : X15 • X16 ≈ X56 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

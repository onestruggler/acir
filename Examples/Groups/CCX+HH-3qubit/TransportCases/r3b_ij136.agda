{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X16 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01356 as E

proved : X36 • X13 ≈ X16 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

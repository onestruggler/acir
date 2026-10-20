{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X15 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01352 as E

proved : X25 • X12 ≈ X15 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

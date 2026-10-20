{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij036 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X06 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01346 as E

proved : X36 • X03 ≈ X06 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij036 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X06 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01308 as E

proved : X03 • X06 ≈ X36 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

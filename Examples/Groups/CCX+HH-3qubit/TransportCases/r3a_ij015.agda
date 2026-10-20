{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij015 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X05 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00066 as E

proved : X01 • X05 ≈ X15 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

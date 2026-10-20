{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij045 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X05 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01310 as E

proved : X04 • X05 ≈ X45 • X04
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X17 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01354 as E

proved : X27 • X12 ≈ X17 • X27
proved = by-assoc-and E.proved Eq.refl Eq.refl

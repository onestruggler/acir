{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij013 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X03 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01336 as E

proved : X13 • X01 ≈ X03 • X13
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij013 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X03 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00064 as E

proved : X01 • X03 ≈ X13 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

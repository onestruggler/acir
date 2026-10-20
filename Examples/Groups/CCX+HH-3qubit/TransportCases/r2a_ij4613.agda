{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4613 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01260 as E

proved : X46 • X13 ≈ X13 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

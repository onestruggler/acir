{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4601 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01254 as E

proved : X46 • X01 ≈ X01 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

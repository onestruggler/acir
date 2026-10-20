{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1546 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01116 as E

proved : X15 • X46 ≈ X46 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

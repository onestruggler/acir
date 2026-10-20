{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X46 ; X47 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01335 as E

proved : X46 • X47 ≈ X67 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

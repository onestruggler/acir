{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X26 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01364 as E

proved : X46 • X24 ≈ X26 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

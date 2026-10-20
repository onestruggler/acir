{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2546 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01176 as E

proved : X25 • X46 ≈ X46 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

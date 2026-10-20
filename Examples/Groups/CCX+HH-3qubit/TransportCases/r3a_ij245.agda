{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X25 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01326 as E

proved : X24 • X25 ≈ X45 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

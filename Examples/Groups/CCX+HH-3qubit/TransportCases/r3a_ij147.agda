{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X17 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01322 as E

proved : X14 • X17 ≈ X47 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij045 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X05 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00036 as E

proved : X45 • X04 ≈ X05 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

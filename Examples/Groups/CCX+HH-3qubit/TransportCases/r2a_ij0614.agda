{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0614 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01046 as E

proved : X06 • X14 ≈ X14 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

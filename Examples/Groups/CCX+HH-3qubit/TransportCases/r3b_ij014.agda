{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij014 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X04 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01337 as E

proved : X14 • X01 ≈ X04 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

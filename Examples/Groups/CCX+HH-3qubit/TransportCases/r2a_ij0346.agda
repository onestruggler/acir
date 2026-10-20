{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01009 as E

proved : X03 • X46 ≈ X46 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

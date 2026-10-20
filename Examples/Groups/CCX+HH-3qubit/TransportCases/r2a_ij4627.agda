{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4627 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01265 as E

proved : X46 • X27 ≈ X27 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

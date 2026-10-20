{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1746 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01147 as E

proved : X17 • X46 ≈ X46 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

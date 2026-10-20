{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X37 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01368 as E

proved : X47 • X34 ≈ X37 • X47
proved = by-assoc-and E.proved Eq.refl Eq.refl

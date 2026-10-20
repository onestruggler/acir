{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X24 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00112 as E

proved : X34 • X23 ≈ X24 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

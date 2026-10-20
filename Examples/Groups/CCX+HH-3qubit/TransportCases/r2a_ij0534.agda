{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0534 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01038 as E

proved : X05 • X34 ≈ X34 • X05
proved = by-assoc-and E.proved Eq.refl Eq.refl

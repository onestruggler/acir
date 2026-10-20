{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0526 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01036 as E

proved : X05 • X26 ≈ X26 • X05
proved = by-assoc-and E.proved Eq.refl Eq.refl

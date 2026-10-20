{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2405 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01151 as E

proved : X24 • X05 ≈ X05 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

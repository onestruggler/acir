{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1205 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00041 as E

proved : X12 • X05 ≈ X05 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

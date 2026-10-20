{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1524 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01110 as E

proved : X15 • X24 ≈ X24 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

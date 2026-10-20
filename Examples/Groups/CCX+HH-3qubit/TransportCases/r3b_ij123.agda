{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X13 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00070 as E

proved : X23 • X12 ≈ X13 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X13 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00076 as E

proved : X12 • X13 ≈ X23 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

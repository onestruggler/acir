{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1207 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00057 as E

proved : X12 • X07 ≈ X07 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

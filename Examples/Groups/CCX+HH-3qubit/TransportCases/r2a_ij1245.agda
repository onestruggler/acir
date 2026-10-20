{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00172 as E

proved : X12 • X45 ≈ X45 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

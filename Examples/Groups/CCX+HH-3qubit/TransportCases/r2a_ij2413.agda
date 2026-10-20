{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2413 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01154 as E

proved : X24 • X13 ≈ X13 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

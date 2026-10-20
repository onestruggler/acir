{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2305 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00042 as E

proved : X23 • X05 ≈ X05 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2314 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00084 as E

proved : X23 • X14 ≈ X14 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

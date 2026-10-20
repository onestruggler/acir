{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2307 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00058 as E

proved : X23 • X07 ≈ X07 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4637 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X37 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01267 as E

proved : X46 • X37 ≈ X37 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

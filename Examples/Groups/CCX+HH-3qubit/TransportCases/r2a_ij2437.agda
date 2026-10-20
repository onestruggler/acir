{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2437 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01160 as E

proved : X24 • X37 ≈ X37 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

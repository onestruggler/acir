{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3704 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01241 as E

proved : X37 • X04 ≈ X04 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

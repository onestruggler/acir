{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3725 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01249 as E

proved : X37 • X25 ≈ X25 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

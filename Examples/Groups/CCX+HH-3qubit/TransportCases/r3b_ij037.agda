{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij037 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X07 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01347 as E

proved : X37 • X03 ≈ X07 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

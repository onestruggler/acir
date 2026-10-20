{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij037 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X07 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01309 as E

proved : X03 • X07 ≈ X37 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

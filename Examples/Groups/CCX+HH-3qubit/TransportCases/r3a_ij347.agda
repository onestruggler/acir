{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X37 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00167 as E

proved : X34 • X37 ≈ X47 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

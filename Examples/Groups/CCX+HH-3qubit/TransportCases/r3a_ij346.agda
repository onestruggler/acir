{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X36 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00160 as E

proved : X34 • X36 ≈ X46 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

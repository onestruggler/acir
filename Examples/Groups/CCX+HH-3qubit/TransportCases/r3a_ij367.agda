{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X36 ; X37 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01334 as E

proved : X36 • X37 ≈ X67 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

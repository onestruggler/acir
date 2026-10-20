{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij067 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X07 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00054 as E

proved : X67 • X06 ≈ X07 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl

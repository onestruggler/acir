{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X46 ; X47 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00183 as E

proved : X67 • X46 ≈ X47 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl

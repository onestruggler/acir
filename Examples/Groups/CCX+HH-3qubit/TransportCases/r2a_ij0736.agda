{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0736 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01070 as E

proved : X07 • X36 ≈ X36 • X07
proved = by-assoc-and E.proved Eq.refl Eq.refl

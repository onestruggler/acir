{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij047 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X07 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01312 as E

proved : X04 • X07 ≈ X47 • X04
proved = by-assoc-and E.proved Eq.refl Eq.refl

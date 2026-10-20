{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X27 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01365 as E

proved : X47 • X24 ≈ X27 • X47
proved = by-assoc-and E.proved Eq.refl Eq.refl

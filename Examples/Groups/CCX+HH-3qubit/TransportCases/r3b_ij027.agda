{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij027 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X07 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01344 as E

proved : X27 • X02 ≈ X07 • X27
proved = by-assoc-and E.proved Eq.refl Eq.refl

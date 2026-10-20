{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij027 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X07 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01305 as E

proved : X02 • X07 ≈ X27 • X02
proved = by-assoc-and E.proved Eq.refl Eq.refl

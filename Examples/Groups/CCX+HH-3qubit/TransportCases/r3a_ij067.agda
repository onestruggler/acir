{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij067 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X07 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01315 as E

proved : X06 • X07 ≈ X67 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

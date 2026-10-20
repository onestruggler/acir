{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X17 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01325 as E

proved : X16 • X17 ≈ X67 • X16
proved = by-assoc-and E.proved Eq.refl Eq.refl

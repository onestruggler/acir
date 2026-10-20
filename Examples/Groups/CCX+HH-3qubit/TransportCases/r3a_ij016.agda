{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij016 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X06 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00067 as E

proved : X01 • X06 ≈ X16 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

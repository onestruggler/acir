{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij012 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00063 as E

proved : X01 • X02 ≈ X12 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

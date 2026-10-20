{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X17 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00104 as E

proved : X12 • X17 ≈ X27 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

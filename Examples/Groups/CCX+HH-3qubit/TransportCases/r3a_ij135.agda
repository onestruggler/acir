{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X15 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01317 as E

proved : X13 • X15 ≈ X35 • X13
proved = by-assoc-and E.proved Eq.refl Eq.refl

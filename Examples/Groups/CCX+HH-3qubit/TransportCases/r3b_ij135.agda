{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X15 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01355 as E

proved : X35 • X13 ≈ X15 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

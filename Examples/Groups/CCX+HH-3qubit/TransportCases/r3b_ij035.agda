{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij035 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X05 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01345 as E

proved : X35 • X03 ≈ X05 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

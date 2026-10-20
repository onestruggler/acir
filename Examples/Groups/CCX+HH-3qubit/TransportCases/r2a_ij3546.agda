{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3546 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01221 as E

proved : X35 • X46 ≈ X46 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

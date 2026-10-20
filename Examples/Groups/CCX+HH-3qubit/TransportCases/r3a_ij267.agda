{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X26 ; X27 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01331 as E

proved : X26 • X27 ≈ X67 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

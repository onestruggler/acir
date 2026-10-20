{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1705 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01137 as E

proved : X17 • X05 ≈ X05 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

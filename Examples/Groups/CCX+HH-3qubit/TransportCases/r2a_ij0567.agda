{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01043 as E

proved : X05 • X67 ≈ X67 • X05
proved = by-assoc-and E.proved Eq.refl Eq.refl

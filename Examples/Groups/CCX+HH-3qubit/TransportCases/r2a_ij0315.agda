{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0315 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01001 as E

proved : X03 • X15 ≈ X15 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

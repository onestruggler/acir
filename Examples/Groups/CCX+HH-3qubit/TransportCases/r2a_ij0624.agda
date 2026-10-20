{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0624 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01050 as E

proved : X06 • X24 ≈ X24 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

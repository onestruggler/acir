{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2406 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01152 as E

proved : X24 • X06 ≈ X06 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

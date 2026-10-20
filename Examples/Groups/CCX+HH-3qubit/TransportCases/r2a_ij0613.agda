{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0613 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01045 as E

proved : X06 • X13 ≈ X13 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

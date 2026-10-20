{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1504 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01106 as E

proved : X15 • X04 ≈ X04 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

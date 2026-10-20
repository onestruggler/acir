{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij025 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X05 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01342 as E

proved : X25 • X02 ≈ X05 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

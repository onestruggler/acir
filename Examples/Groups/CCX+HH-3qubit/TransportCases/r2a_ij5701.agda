{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5701 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01284 as E

proved : X57 • X01 ≈ X01 • X57
proved = by-assoc-and E.proved Eq.refl Eq.refl

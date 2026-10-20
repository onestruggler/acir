{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij024 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X04 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01341 as E

proved : X24 • X02 ≈ X04 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3601 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01224 as E

proved : X36 • X01 ≈ X01 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00177 as E

proved : X01 • X46 ≈ X46 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

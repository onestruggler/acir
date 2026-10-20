{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00130 as E

proved : X01 • X26 ≈ X26 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

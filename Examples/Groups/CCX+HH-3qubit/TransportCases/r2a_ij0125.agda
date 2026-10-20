{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00123 as E

proved : X01 • X25 ≈ X25 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

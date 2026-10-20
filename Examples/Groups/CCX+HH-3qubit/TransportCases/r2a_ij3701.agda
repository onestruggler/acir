{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3701 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01239 as E

proved : X37 • X01 ≈ X01 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

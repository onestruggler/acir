{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3716 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01247 as E

proved : X37 • X16 ≈ X16 • X37
proved = by-assoc-and E.proved Eq.refl Eq.refl

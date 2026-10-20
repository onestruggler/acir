{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2716 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01202 as E

proved : X27 • X16 ≈ X16 • X27
proved = by-assoc-and E.proved Eq.refl Eq.refl

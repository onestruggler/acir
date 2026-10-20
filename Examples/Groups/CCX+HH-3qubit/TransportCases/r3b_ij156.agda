{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X16 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00094 as E

proved : X56 • X15 ≈ X16 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

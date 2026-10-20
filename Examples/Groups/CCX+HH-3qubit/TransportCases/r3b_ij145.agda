{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X15 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00086 as E

proved : X45 • X14 ≈ X15 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

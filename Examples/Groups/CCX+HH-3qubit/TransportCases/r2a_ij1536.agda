{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1536 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01114 as E

proved : X15 • X36 ≈ X36 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

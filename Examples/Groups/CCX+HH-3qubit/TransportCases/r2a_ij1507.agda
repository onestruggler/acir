{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1507 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01108 as E

proved : X15 • X07 ≈ X07 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

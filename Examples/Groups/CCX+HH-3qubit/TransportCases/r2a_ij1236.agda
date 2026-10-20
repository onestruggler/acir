{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00158 as E

proved : X12 • X36 ≈ X36 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

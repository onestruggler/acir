{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2436 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01159 as E

proved : X24 • X36 ≈ X36 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

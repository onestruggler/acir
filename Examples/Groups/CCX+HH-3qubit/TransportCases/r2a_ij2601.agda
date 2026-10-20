{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2601 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01179 as E

proved : X26 • X01 ≈ X01 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

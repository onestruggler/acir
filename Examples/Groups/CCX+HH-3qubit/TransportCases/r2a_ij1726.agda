{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1726 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01142 as E

proved : X17 • X26 ≈ X26 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

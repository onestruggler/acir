{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2417 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01157 as E

proved : X24 • X17 ≈ X17 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1734 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01143 as E

proved : X17 • X34 ≈ X34 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

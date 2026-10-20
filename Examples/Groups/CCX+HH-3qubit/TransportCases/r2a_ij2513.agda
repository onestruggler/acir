{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2513 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01169 as E

proved : X25 • X13 ≈ X13 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

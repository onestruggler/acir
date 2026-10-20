{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0714 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01061 as E

proved : X07 • X14 ≈ X14 • X07
proved = by-assoc-and E.proved Eq.refl Eq.refl
